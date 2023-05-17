from pathlib import Path
from subprocess import run

passed = 0
failed = 0

print("Lexer tests:")
for test_path in Path("lexer_tests").iterdir():
    with test_path.open("rb") as testfile:
        content = testfile.read()
        code, expected = content.split(b"//" + b"-" * 80)
        expected = expected.strip()
        result = run(f"antlr4-parse Bosco.g4 program -tokens", input=code.strip(), shell=True, capture_output=True)
        actual = result.stdout.strip()
        if actual == expected.strip():
            passed += 1
            print(f"{test_path.name:<50} OK")
        else:
            failed +=1
            print(f"{test_path.name:<50} FAIL")
            print()
            print("EXPECTED:")
            print(expected)
            print("ACTUAL:")
            print(actual)

print("Parser tests:")
for test_path in Path("tests").iterdir():
    with test_path.open("rb") as testfile:
        content = testfile.read()
        code, expected = content.split(b"//" + b"-" * 80)
        expected = expected.strip()
        result = run(f"antlr4-parse Bosco.g4 program -tree", input=code.strip(), shell=True, capture_output=True)
        actual = result.stdout.strip()
        if actual == expected.strip():
            passed += 1
            print(f"{test_path.name:<50} OK")
        else:
            failed +=1
            print(f"{test_path.name:<50} FAIL")
            print()
            print("EXPECTED:")
            print(expected)
            print("ACTUAL:")
            print(actual)

print()
print(f"Passed tests: {passed}")
print(f"Failed tests: {failed}")