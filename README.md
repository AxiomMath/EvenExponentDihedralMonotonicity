[![](logo.svg)](https://axiommath.ai/)

# Even-Exponent Dihedral Monotonicity

This is a Lean formalization of the monotonicity of even-exponent distances for
continuous-time random walks on dihedral groups.

## Main Results

* For every `n ≥ 2` and every `m ≥ 1`, raising the jump rates of a symmetric walk on the
  dihedral group `D_n` cannot increase the `ℓ^{2m}` distance of its time-`t` distribution
  from uniform.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results
claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only
depends on the dependency above. It contains formal statements of
[§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean
comparator on a Linux machine. First, follow the instructions in
https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
