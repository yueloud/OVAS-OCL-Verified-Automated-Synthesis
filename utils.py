import re
import os
import json
import time
from google import genai
from google.genai import types
from pydantic import BaseModel
from config import CURRENT_MODEL, TEMPERATURE

# 确保你在环境变量中设置了 GEMINI_API_KEY
client = genai.Client()

# ========== 瞬时错误判定 ==========
TRANSIENT_ERROR_CODES = {429, 500, 502, 503, 504}
TRANSIENT_ERROR_KEYWORDS = ["high demand", "overloaded", "rate limit", "temporarily", "try again"]
MAX_API_RETRIES = 5  # API 层最大重试次数
BASE_DELAY_SECONDS = 2  # 初始等待秒数
MAX_DELAY_SECONDS = 60  # 最大等待秒数


def is_transient_error(error: Exception) -> bool:
    """判断是否为可重试的瞬时错误"""
    err_str = str(error).lower()

    # 检查 HTTP 状态码
    for code in TRANSIENT_ERROR_CODES:
        if str(code) in err_str:
            return True

    # 检查关键词
    for keyword in TRANSIENT_ERROR_KEYWORDS:
        if keyword in err_str:
            return True

    return False


def clean_code_block(text: str) -> str:
    """精确剥离 Markdown 格式"""
    if not text:
        return ""
    match = re.search(r"```(?:\w+)?\n(.*?)```", text, re.DOTALL)
    return match.group(1).strip() if match else text.strip()


def get_multiline_input(prompt_text: str) -> str:
    print(f"\n{prompt_text}\n(Type/Paste text. Press Enter twice to finish)")
    lines = []
    while True:
        try:
            line = input()
            if line == "":
                break
            lines.append(line)
        except EOFError:
            break
    return "\n".join(lines)


def call_llm_structured(prompt: str, system_instruction: str, response_schema: type[BaseModel]) -> str:
    """带 JSON Schema 约束解码 + 指数退避重试的 LLM 调用"""

    # 1. 动态生成 Pydantic 的 JSON Schema 字典并转为字符串
    schema_dict = response_schema.model_json_schema()
    schema_str = json.dumps(schema_dict, indent=2)

    # 2. 强行将 Schema 拼接到 System Instruction 中
    augmented_instruction = (
        f"{system_instruction}\n\n"
        f"【CRITICAL JSON SCHEMA CONSTRAINT】\n"
        f"You MUST output ONLY a valid raw JSON object. Do not wrap it in markdown block. "
        f"Your output JSON MUST strictly conform to the following JSON Schema (including resolving all $defs):\n"
        f"{schema_str}"
    )

    # 3. 配置 Config
    config = types.GenerateContentConfig(
        system_instruction=augmented_instruction,
        temperature=TEMPERATURE,
        response_mime_type="application/json",
    )

    # 4. 带指数退避的 API 调用
    for attempt in range(1, MAX_API_RETRIES + 1):
        try:
            response = client.models.generate_content(
                model=CURRENT_MODEL,
                contents=prompt,
                config=config
            )
            return clean_code_block(response.text)

        except Exception as e:
            if is_transient_error(e):
                # 瞬时错误：计算退避时间，等待后重试
                delay = min(BASE_DELAY_SECONDS * (2 ** (attempt - 1)), MAX_DELAY_SECONDS)
                # 加一点随机抖动，避免惊群
                jitter = delay * 0.1
                actual_delay = delay + jitter

                print(f"  ⏳ [API 瞬时错误] 第 {attempt}/{MAX_API_RETRIES} 次，"
                      f"{actual_delay:.1f}s 后重试... ({e})")
                time.sleep(actual_delay)

                if attempt == MAX_API_RETRIES:
                    # API 层重试用尽，向上抛出
                    print(f"  🚨 API 层重试 {MAX_API_RETRIES} 次后仍失败，放弃此调用。")
                    raise e
            else:
                # 非瞬时错误（如 400 Bad Request、认证失败等），直接抛出
                raise e

    # 理论上不会走到这里
    raise RuntimeError("API 调用意外终止")

