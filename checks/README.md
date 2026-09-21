# Verification

From the repository root:

```sh
lake exe cache get
lake build Eden Solution
python3 checks/check_axioms.py
lake build Challenge
```

The Python script runs both `#print axioms` files, checks that all 219 final
and 777 supporting declarations appear, and checks their axioms against
`propext`, `Classical.choice` and `Quot.sound`. It uses the Python standard
library. On Windows, use `python` in place of `python3`.

`Challenge.lean` specifies the 219 final statements with deliberate proof
placeholders. `Solution.lean` proves them and imports only `Eden`.

## Lean Comparator

[Lean Comparator](https://github.com/leanprover/comparator) compares the
statements in `Challenge` and `Solution`, enforces the axiom list in
`comparator.json`, and replays the exported proofs with the Lean kernel.

The checked tool revisions are:

| Tool | Revision |
| --- | --- |
| Lean | `v4.33.1` (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) |
| Comparator | `c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809` |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

Comparator requires Linux with Landlock, a non-root account and a user
systemd session. The supplied command also uses Bubblewrap. Install Go
1.24.0 to build the pinned Landrun revision. In a separate tools directory:

```sh
git clone https://github.com/leanprover/comparator.git
git -C comparator checkout --detach c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809
printf 'leanprover/lean4:v4.33.1\n' > comparator/lean-toolchain
(cd comparator && lake build comparator lean4export)
git -C comparator/.lake/packages/lean4export rev-parse HEAD

git clone https://github.com/Zouuup/landrun.git
git -C landrun checkout --detach 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
(cd landrun && go build -trimpath -o landrun ./cmd/landrun)
```

The exporter revision printed above should match the table. The only
Comparator source change is its toolchain selection from 4.33.0 to 4.33.1.
Add the resulting `comparator`, `lean4export` and `landrun` binaries to
`PATH`. Alternatively, the latter two paths may be supplied through
`COMPARATOR_LEAN4EXPORT` and `COMPARATOR_LANDRUN`.

Use a fresh copy of this repository for the comparison. Download the
dependency cache before invoking the sandbox:

```sh
lake exe cache get
bash checks/run_comparator.sh
```

The sandbox gives the process write access to `.lake` and restricts socket
access. Comparator compiles the challenge and solution separately. Its
success output includes:

```text
Lean default kernel accepts the solution
Your solution is okay!
```

The GitHub workflow compiles the proofs and checks the axiom reports.
Comparator is a separate Linux check.
