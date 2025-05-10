# Cod_MPI_Activiate2
#!/usr/bin/env python3

from collections import defaultdict
import sys

Literal = int
Clause = list[int]
CNF = list[Clause]


def _parse_clauses(raw: list[str]) -> tuple[CNF, dict[str, int]]:
    varmap = {}
    next_id = 1
    clauses = []
    for line in raw:
        lits = []
        for token in line.replace('v', ' ').split():
            neg = token.startswith(('~', '!'))
            if neg:
                token = token[1:]
            if not token:
                continue
            if token not in varmap:
                varmap[token] = next_id
                next_id += 1
            lit = varmap[token]
            lits.append(-lit if neg else lit)
        if not lits:
            raise ValueError('Clauză goală.')
        clauses.append(lits)
    return clauses, varmap


def _pretty_assignment(assignment: dict[int, bool], varmap: dict[str, int]) -> str:
    inv = {v: k for k, v in varmap.items()}
    return ', '.join(f"{inv[v]}={'A' if val else 'F'}" for v, val in sorted(assignment.items()))


# Davis–Putnam elimination ---------------------------------------------------

def _dp(clauses: CNF) -> tuple[bool, dict[int, bool]]:
    clauses = [c[:] for c in clauses]
    assignment = {}
    while clauses:
        var = abs(clauses[0][0])
        pos = [c for c in clauses if var in c]
        neg = [c for c in clauses if -var in c]
        resolvents = []
        for c1 in pos:
            for c2 in neg:
                new = [lit for lit in c1 if lit != var] + [lit for lit in c2 if lit != -var]
                if any(l in new and -l in new for l in new):
                    continue
                new = list(dict.fromkeys(new))
                if not new:
                    return False, {}
                resolvents.append(new)
        clauses = [c for c in clauses if var not in c and -var not in c]
        clauses.extend(resolvents)
        if not clauses:
            return True, assignment
    return True, assignment


# DPLL -----------------------------------------------------------------------

def _unit_propagate(clauses: CNF, assignment: dict[int, bool]) -> tuple[bool, CNF]:
    changed = True
    while changed:
        changed = False
        unit = None
        for c in clauses:
            unassigned = [lit for lit in c if abs(lit) not in assignment]
            if len(unassigned) == 0:
                if not any((lit > 0) == assignment.get(abs(lit), False) for lit in c):
                    return False, clauses
            elif len(unassigned) == 1:
                unit = unassigned[0]
                break
        if unit is not None:
            val = unit > 0
            assignment[abs(unit)] = val
            new_clauses = []
            for c in clauses:
                if (unit > 0 and unit in c) or (unit < 0 and unit in c):
                    continue
                new_c = [lit for lit in c if lit != -unit]
                new_clauses.append(new_c)
            clauses = new_clauses
            changed = True
    return True, clauses


def _pure_literal_assign(clauses: CNF, assignment: dict[int, bool]) -> CNF:
    literals = [lit for c in clauses for lit in c]
    counts = defaultdict(int)
    for lit in literals:
        counts[lit] += 1
    for lit in list(counts):
        if -lit in counts or abs(lit) in assignment:
            continue
        assignment[abs(lit)] = lit > 0
        clauses = [c for c in clauses if lit not in c]
    return clauses


def _dpll(clauses: CNF, assignment: dict[int, bool]) -> bool:
    ok, clauses = _unit_propagate(clauses, assignment)
    if not ok:
        return False
    clauses = _pure_literal_assign(clauses, assignment)
    if not clauses:
        return True
    lit = clauses[0][0]
    var = abs(lit)
    for val in (True, False):
        if var in assignment and assignment[var] != val:
            continue
        local_assignment = assignment.copy()
        local_assignment[var] = val
        new_clauses = []
        conflict = False
        for c in clauses:
            if (val and lit in c) or (not val and -lit in c):
                continue
            new_c = [l for l in c if l != (-lit if val else lit)]
            if not new_c:
                conflict = True
                break
            new_clauses.append(new_c)
        if not conflict and _dpll(new_clauses, local_assignment):
            assignment.clear()
            assignment.update(local_assignment)
            return True
    return False


def dpll(clauses: CNF) -> tuple[bool, dict[int, bool]]:
    assignment = {}
    sat = _dpll([c[:] for c in clauses], assignment)
    return sat, assignment


# Rezoluție ------------------------------------------------------------------

def resolution_refutation(clauses: CNF) -> bool:
    new = set()
    clauses = [tuple(c) for c in clauses]
    while True:
        n = len(clauses)
        for i in range(n):
            for j in range(i + 1, n):
                ci, cj = clauses[i], clauses[j]
                for lit in ci:
                    if -lit in cj:
                        resolvent = tuple(sorted(set(ci) | set(cj) - {lit, -lit}))
                        if not resolvent:
                            return False
                        new.add(resolvent)
        if new.issubset(set(clauses)):
            return True
        for c in new:
            if c not in clauses:
                clauses.append(c)


# CLI ------------------------------------------------------------------------

def _banner():
    print("========================================")
    print("Rezolvator simplu SAT")
    print("========================================")


def _read_instance():
    n = int(input("Numărul de clauze: ").strip())
    raw = [input(f"Clauza {i + 1}: ") for i in range(n)]
    return _parse_clauses(raw)


def main() -> None:
    _banner()
    while True:
        print("\nAlege metoda:\n 1) Eliminare Davis–Putnam (DP)\n 2) Căutare DPLL\n 3) Refutare prin rezoluție\n 4) Ieșire")
        choice = input("Selectează: ").strip()
        if choice == '4':
            print("La revedere!")
            return
        clauses, varmap = _read_instance()
        if choice == '1':
            sat, assign = _dp(clauses)
        elif choice == '2':
            sat, assign = dpll(clauses)
        elif choice == '3':
            sat = resolution_refutation(clauses)
            assign = {}
        else:
            print("Selecție invalidă.")
            continue
        if sat:
            print("SATISFIABIL")
            if assign:
                print("Atribuire:", _pretty_assignment(assign, varmap))
            else:
                print("(Această metodă nu produce o atribuire.)")
        else:
            print("NESATISFIABIL")


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        print("\nOprire.", file=sys.stderr)
        sys.exit(1)
