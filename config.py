import os

CURRENT_MODEL = os.getenv("LLM_BACKEND", "gemini-3-flash-preview")
# 形式化验证必须追求确定性，禁止高温度产生语法幻觉
TEMPERATURE = 0.0 
MAX_RETRIES = 5