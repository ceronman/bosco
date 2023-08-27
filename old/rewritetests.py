from pathlib import Path
from subprocess import run


for test_path in Path("tests").iterdir():
    print(f"Rewriting {test_path}")
    with test_path.open("rb") as testfile:
        code, _ = testfile.read().split(b"//" + b"-" * 80)
        code = code.strip()

    with Path("snippet.bosco").open("wb") as snippet:
        snippet.write(code)

    result = run(f"python3 addtest.py {test_path.name}", input=code, shell=True, capture_output=True)

for test_path in Path("lexer_tests").iterdir():
    print(f"Rewriting {test_path}")
    with test_path.open("rb") as testfile:
        code, _ = testfile.read().split(b"//" + b"-" * 80)
        code = code.strip()

    with Path("snippet.bosco").open("wb") as snippet:
        snippet.write(code)

    result = run(f"python3 addtest.py -l {test_path.name}", input=code, shell=True, capture_output=True)