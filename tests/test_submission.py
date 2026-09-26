from pathlib import Path
import re
import shutil
import subprocess

APP = Path('/app/Solution.lean')
PROJECT = Path('/mathlib/Submission')
CHECKER = PROJECT / 'Checker.lean'

EXPECTED_NAMES = {
    'lagrange_coeff_formula',
    'lagrange_coeff_card_sub_three',
    'barycentric_moment_identity',
}

ALLOWED_AXIOMS = {
    'propext',
    'Classical.choice',
    'Quot.sound',
}


def run_lean() -> str:
    PROJECT.mkdir(parents=True, exist_ok=True)
    shutil.copy2(APP, PROJECT / 'Solution.lean')
    CHECKER.write_text((Path('/tests') / 'Checker.lean').read_text())
    proc = subprocess.run(
        ['bash', '-lc', 'cd /mathlib && lake env lean Submission/Checker.lean'],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=900,
    )
    if proc.returncode != 0:
        raise AssertionError(proc.stdout)
    return proc.stdout


def parse_axiom_lines(output: str):
    lines = [line.strip() for line in output.splitlines() if 'axioms:' in line]
    assert len(lines) == 3, f'expected three axiom reports, got: {lines}'
    found = []
    for line in lines:
        _, rhs = line.split('axioms:', 1)
        rhs = rhs.strip().strip('{}[]()')
        names = [x.strip() for x in rhs.split(',') if x.strip()]
        found.append(set(names))
    return found


def test_submission_compiles_and_has_required_theorems():
    assert APP.exists(), 'missing /app/Solution.lean'
    source = APP.read_text(encoding='utf-8')
    assert 'sorry' not in source.lower()
    assert 'admit' not in source.lower()
    assert re.search(r'(?m)^\s*(?:theorem|lemma)\s+lagrange_coeff_formula\b', source)
    assert re.search(r'(?m)^\s*(?:theorem|lemma)\s+lagrange_coeff_card_sub_three\b', source)
    assert re.search(r'(?m)^\s*(?:theorem|lemma)\s+barycentric_moment_identity\b', source)

    forbidden = [
        'Lagrange.coeff_eq_sum',
        'Lagrange.eval_iterate_derivative_eq_sum',
        'native_decide',
        'implemented_by',
    ]
    assert not any(token in source for token in forbidden), 'forbidden shortcut detected'
    assert re.search(r'(?m)^\s*(?:axiom|unsafe\s+theorem|unsafe\s+def)\b', source) is None, 'unsafe or user-defined axiom declaration detected'

    out = run_lean()
    for theorem_name in EXPECTED_NAMES:
        assert theorem_name in out, f'{theorem_name} not mentioned by checker output'

    for axioms in parse_axiom_lines(out):
        assert 'sorryAx' not in axioms, f'sorry axiom present: {axioms}'
        assert axioms <= ALLOWED_AXIOMS, f'unapproved axiom dependency: {axioms}'


def test_checker_is_not_using_the_reference_solution():
    checker = (Path('/tests') / 'Checker.lean').read_text(encoding='utf-8')
    assert '/solution/' not in checker.lower()
    assert 'solve.sh' not in checker.lower()
