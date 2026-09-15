from pathlib import Path
import hashlib, json
ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / "verification/source-inventory.json").read_text())
for rel, expected in data["files"].items():
    p = ROOT / rel
    assert p.is_file() and not p.is_symlink(), rel
    with p.open("rb") as f:
        assert hashlib.file_digest(f, "sha256").hexdigest() == expected, rel
print(f"PASS: {len(data['files'])} publication files match their SHA-256 inventory.")
print("This is a source-integrity check, not a Lean build or a proof of the main theorem.")
