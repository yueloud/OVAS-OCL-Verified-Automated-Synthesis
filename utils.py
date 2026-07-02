import re
import json
import time
from google import genai
from google.genai import types
from pydantic import BaseModel
from config import CURRENT_MODEL, TEMPERATURE, AblationSwitch
from typing import Optional

client = genai.Client()

TRANSIENT_ERROR_CODES = {429, 500, 502, 503, 504}
TRANSIENT_ERROR_KEYWORDS = ["high demand", "overloaded", "rate limit", "temporarily", "try again"]
MAX_API_RETRIES = 5
BASE_DELAY_SECONDS = 2
MAX_DELAY_SECONDS = 60

def is_transient_error(error: Exception) -> bool:
    err_str = str(error).lower()

    for code in TRANSIENT_ERROR_CODES:
        if str(code) in err_str:
            return True

    for keyword in TRANSIENT_ERROR_KEYWORDS:
        if keyword in err_str:
            return True
    return False

def clean_code_block(text: str) -> str:

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

def call_llm_structured(prompt: str, system_instruction: str, response_schema: type[BaseModel], ablation_config: Optional[AblationSwitch] = None) -> str:

    use_schema_constraint = True
    if ablation_config is not None:
        use_schema_constraint = ablation_config.is_enabled("enable_schema_constraint")

    base_instruction = system_instruction if system_instruction else ""

    if use_schema_constraint:

        schema_dict = response_schema.model_json_schema()
        schema_str = json.dumps(schema_dict, indent=2)
        augmented_instruction = (
            f"{base_instruction}\n\n"
            f"[CRITICAL JSON SCHEMA CONSTRAINT]\n"
            f"You MUST output ONLY a valid raw JSON object. Do not wrap it in markdown block. "
            f"Your output JSON MUST strictly conform to the following JSON Schema (including resolving all $defs):\n"
            f"{schema_str}"
        )
        config = types.GenerateContentConfig(
            system_instruction=augmented_instruction,
            temperature=TEMPERATURE,
            response_mime_type="application/json",
            max_output_tokens=65536,
        )
    else:

        config = types.GenerateContentConfig(
            system_instruction=base_instruction,
            temperature=TEMPERATURE,
            max_output_tokens=65536,
        )


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

                delay = min(BASE_DELAY_SECONDS * (2 ** (attempt - 1)), MAX_DELAY_SECONDS)

                jitter = delay * 0.1
                actual_delay = delay + jitter

                time.sleep(actual_delay)
                if attempt == MAX_API_RETRIES:
                    print(f" API error")
                    raise e
            else:
                raise e

    raise RuntimeError("API error")

