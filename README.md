# Weak 3-randomness reflection does not imply Luzin’s property (N)

[中文](README.zh-CN.md) · [Paper (PDF)](paper/Weak_3_Randomness_and_Luzin_N.pdf) · [TeX source](paper/Weak_3_Randomness_and_Luzin_N.tex) · [Main theorem in Lean](Weak_3_Randomness_and_Luzin_N/GuoMain.lean)

For every 0 < ε < 1, there is a Type-2 computable continuous real function that reflects both weak 3-randomness and Martin-Löf randomness relative to the second Turing jump, yet maps a compact null set to a set of Lebesgue measure at least 1 − ε.

## Reproduce the proof

With Lean 4.32.2 and the pinned mathlib v4.32.2 dependency, run these commands from the project root:

```sh
lake build -Kjobs=4
lake env lean Axioms.lean
```

## Formalization

The full statement of Theorem 1.1 is formalized using the test definitions in Section 2. The project also proves Theorem 2.1, Lemmas 2.2, 3.1, 4.1 and 4.2, and the computable extension of Lemma 5.2. The [module guide](Weak_3_Randomness_and_Luzin_N.lean) maps the paper to Lean declarations.

For Lemma 5.1, the development proves the homeomorphism and the measure-scaling identity. It does not separately state that finite prefixes of the inverse address can be computed from an arbitrary fast Cauchy name of a point in the embedded Cantor set. The proof of Theorem 1.1 directly establishes the [uniform effective pullback of test layers](Weak_3_Randomness_and_Luzin_N/GuoRealOraclePullback.lean#L228-L261).

At [commit 4c52dff](https://github.com/FAlepher/Weak_3_Randomness_and_Luzin_N/tree/4c52dff0973a7c2d9239bfe6c534c9066283b390), the [axiom audit](Axioms.lean) reported only `propext`, `Classical.choice`, and `Quot.sound` for Theorem 1.1. The [audit output](docs/axioms.log) lists all seven checked declarations.

## Licenses

The Lean source code is licensed under [Apache-2.0](LICENSE). The manuscript in `paper/` is licensed under [CC BY 4.0](paper/LICENSE).
