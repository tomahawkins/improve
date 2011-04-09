# ImProve

ImProve is an imperative programming language embedded in [Haskell](http://haskell.org/) for
high assurance applications.  ImProve uses infinite state, unbounded
model checking to verify programs adhere to specifications.
[Yices](http://yices.csl.sri.com/) (required) is the backend SMT solver.

ImProve compiles to C, [Simulink](http://www.mathworks.com/products/simulink/), and [Modelica](http://www.modelica.org/)
for implementation and system simulation.

## Links

- [ImProve Homepage](http://github.com/tomahawkins/improve/wiki/ImProve)
- [ImProve Hackage Library](http://hackage.haskell.org/package/improve)

# Release Notes

0.3.4    ???

- Exported var and zero.

0.3.3    04/07/11

- Modelica model generation.
- 'assume' returns 'Theorem' types to act as lemmas to other theorems.
  Assumptions are not longer applied program wide.
- Added #ifdef __cplusplus to generated C header.
- Fixed conditionals for assertions in Simulink generation.

0.3.2    04/02/11

- Apply lemmas in all inductive steps except the last (instead of just at the begining).
- Removed hidden step 1.

0.3.1    03/28/11

- Simulink remove null effect optimization.
- Haddock documentation.

0.3.0    03/28/11

- Simulink model generation.
- Removed UV types.

0.2.3    12/13/10

- Fixed haddock documentation.

0.2.2    12/12/10

- Theorem name formatting (removed unique identifer).
- Better trace formatting.

0.2.1    12/09/10

- bugfix: lemmas referenced in induction step.

0.2.0    12/08/10

- Released 'assert' with 'theorem', which provides control of k
  and the ability to provide lemmas to simplify the proof.
- Verification assumes property is true for inductive steps up to k.
  Reduces the number of steps to converge on proof for some invariants.

0.1.6    12/02/10

- Made Statement an instance of Show.
- Made V a an instance of Eq and Ord.
- Created untyped variables (UV) and extended varInfo.
- Bugfix: shadow variable in Label collides with structure name.

0.1.5    11/23/10

- Loosened mtl requirements (mtl < 2.1).

0.1.4    11/22/10

- Bugfix: verification programming trimming: expressions in assertions in if statements not captured.
- Better annotation for assertions.

0.1.3    11/18/10

- Started state space narrowing optimizations: simple code analysis
  that reduce narrow the reachable state, thus reducing the
  number of inconclusive results.

