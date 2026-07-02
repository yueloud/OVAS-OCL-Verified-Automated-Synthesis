import os
import json
import copy
from typing import Any, Dict, List, Optional

CURRENT_MODEL = os.getenv("LLM_BACKEND", "gemini-3.1-pro-preview")

TEMPERATURE = 0.0
MAX_RETRIES = 5


class Dict2Obj:

    def __init__(self, data: Dict[str, Any], _root: Optional["Dict2Obj"] = None):

        object.__setattr__(self, '_data', data)
        object.__setattr__(self, '_root', _root if _root is not None else self)

        for key, value in data.items():
            if isinstance(value, dict):
                converted = Dict2Obj(value, _root=self._root)
            elif isinstance(value, list):
                converted = [
                    Dict2Obj(item, _root=self._root) if isinstance(item, dict) else item
                    for item in value
                ]
            else:
                converted = value
            object.__setattr__(self, key, converted)

    def __getattr__(self, name: str) -> Any:
        if name.startswith('_'):
            raise AttributeError(name)
        return None

    def __contains__(self, key: str) -> bool:
        return key in self._data

    def __getitem__(self, key: str) -> Any:
        return getattr(self, key)

    def __repr__(self) -> str:
        return f"Dict2Obj({self._data})"

    def to_dict(self) -> Dict[str, Any]:

        result = {}
        for key, value in self._data.items():
            attr = getattr(self, key)
            if isinstance(attr, Dict2Obj):
                result[key] = attr.to_dict()
            elif isinstance(attr, list):
                result[key] = [
                    item.to_dict() if isinstance(item, Dict2Obj) else item
                    for item in attr
                ]
            else:
                result[key] = attr
        return result

    def keys(self) -> List[str]:
        return list(self._data.keys())

    def values(self) -> List[Any]:
        return [getattr(self, k) for k in self._data.keys()]

    def items(self):
        for k in self._data.keys():
            yield k, getattr(self, k)

    def get(self, key: str, default: Any = None) -> Any:
        val = getattr(self, key)
        return val if val is not None else default

    def ablation_root(self) -> "Dict2Obj":
        return self._root

class AblationSwitch:
    DEFAULT_SWITCHES = {
        "enable_layer1_json_schema": True,
        "enable_layer2_semantic": True,
        "enable_layer2_type_check": True,
        "enable_layer2_null_safety": True,
        "enable_layer3_z3_compile": True,
        "enable_layer3_z3_equivalence": True,
        "enable_safety_injection": True,
        "enable_vacuity_check": True,
        "enable_CGSC": True,
        "enable_system_instruction": True,
        "enable_schema_constraint": True,
        "schema_variant": "full",
    }

    PRESETS = {
        "full_pipeline": {
            "description": "All switches on",
            "overrides": {},
        },
        "exp1_pre_verification": {
            "description": "Informal parts ablation",
            "overrides": {
                "enable_system_instruction": False,
                "enable_layer1_json_schema": False,
                "enable_layer2_semantic": False,
                "enable_layer2_type_check": False,
                "enable_layer2_null_safety": False,
            },
        },
        "exp2_post_feedback": {
            "description": "Formal parts ablation",
            "overrides": {
                "enable_CGSC": False,
            },
        },
    }

    def __init__(self, preset: Optional[str] = None,
                 overrides: Optional[Dict[str, Any]] = None,
                 json_path: Optional[str] = None):


        self._switches = dict(self.DEFAULT_SWITCHES)
        self._meta = {
            "preset": preset or "custom",
            "overrides_applied": [],
        }


        if json_path:
            self._load_from_json(json_path)
        elif preset:
            if preset not in self.PRESETS:
                raise ValueError(
                    f"Unknown preset: '{preset}'. Available: {list(self.PRESETS.keys())}"
                )
            for key, value in self.PRESETS[preset]["overrides"].items():
                self._switches[key] = value
                self._meta["overrides_applied"].append(key)


        if overrides:
            for key, value in overrides.items():
                if key not in self.DEFAULT_SWITCHES:
                    raise ValueError(
                        f"Unknown switch: '{key}'. Available: {list(self.DEFAULT_SWITCHES.keys())}"
                    )
                self._switches[key] = value
                self._meta["overrides_applied"].append(key)


        self._obj = Dict2Obj(self._switches)

    def _load_from_json(self, path: str):

        with open(path, 'r', encoding='utf-8') as f:
            payload = json.load(f)
        switches = payload.get("switches", payload)
        for key, value in switches.items():
            if key in self.DEFAULT_SWITCHES:
                self._switches[key] = value
        self._meta = payload.get("meta", self._meta)


    def __getattr__(self, name: str) -> Any:
        if name.startswith('_'):
            raise AttributeError(name)
        return getattr(self._obj, name)

    def __contains__(self, key: str) -> bool:
        return key in self._switches

    def __getitem__(self, key: str) -> Any:
        return self._switches[key]


    def is_enabled(self, switch_name: str) -> bool:

        val = self._switches.get(switch_name)
        if val is None:
            raise ValueError(f"Unknown switch: '{switch_name}'")
        return bool(val)

    def get_variant(self) -> str:

        return self._switches.get("schema_variant", "full")

    def to_dict(self) -> Dict[str, Any]:

        return copy.deepcopy(self._switches)

    def to_json(self, path: str):

        payload = {
            "meta": {
                **self._meta,
                "export_time": __import__("datetime").datetime.now().isoformat(),
            },
            "switches": self._switches,
        }
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(payload, f, indent=2, ensure_ascii=False)

    @classmethod
    def from_json(cls, path: str) -> "AblationSwitch":

        return cls(json_path=path)

    @classmethod
    def list_presets(cls) -> Dict[str, str]:

        return {name: info["description"] for name, info in cls.PRESETS.items()}

    def diff_from_default(self) -> Dict[str, Dict[str, Any]]:

        diff = {}
        for key, default_val in self.DEFAULT_SWITCHES.items():
            current_val = self._switches[key]
            if current_val != default_val:
                diff[key] = {"default": default_val, "current": current_val}
        return diff

    def summary(self) -> str:

        diff = self.diff_from_default()
        if not diff:
            return "AblationSwitch(full_pipeline)"
        lines = ["AblationSwitch("]
        for key, vals in diff.items():
            lines.append(f"  {key}: default={vals['default']} -> current={vals['current']}")
        lines.append(")")
        return "\n".join(lines)

    def __repr__(self) -> str:
        return self.summary()
