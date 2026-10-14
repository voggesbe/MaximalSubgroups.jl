# MaximalSubgroups.jl

Julia package for the algebraic analysis of **maximal subgroups** via root
systems. Given an irreducible root system `R` (types `A`, `B`, `C`, `D`, `E`)
and a *quasimaximal subsystem* described by a descriptor, the package:

- computes the **anisotropic system** `φₐ` associated to the subsystem,
- builds the **diagram-automorphism permutation** `f` that attaches to a
  subsystem of type `A` or `D`,
- converts a root-index permutation into its **permutation matrix** `F`.

## Installation

The package depends on [Oscar](https://github.com/H4cker/Oscar) (and its
dependencies). Clone the repository, activate its environment, and let Julia
resolve the required packages:

```bash
# 1. clone the package
git clone https://github.com/<your-username>/MaximalSubgroups.jl.git
cd MaximalSubgroups.jl

# 2. start Julia from inside the package directory
julia

# 3. activate the package environment and install the dependencies
julia> using Pkg
julia> Pkg.instantiate()        # resolves from Project.toml
# Julia, or Pkg.resolve()  # ...or Pkg.resolve() if a Manifest.toml already exists
```
`Pkg.instantiate()` downloads and precompiles everything the package needs
(including Oscar) the first time you `using MaximalSubgroups`. Re-running it
later is cheap and keeps the environment in sync if Project.toml changes.
If you have a committed `Manifest.toml` and want an exact, reproducible
environment, instantiate with `--manifest`.

To update to the latest version of the package:
```bash
cd MaximalSubgroups.jl
git pull
julia -e 'using Pkg; Pkg.instantiate()'
```
## Usage

```julia

using MaximalSubgroups

R = root_system(:B, 8)

# v — quasimaximal subsystem descriptor
# w   anisotropic (black) node descriptor
# f   automorphism permutation (use cperm() or diagram_automorphism)
Phi_a, I, B, s_R, F = p_a(R, [(:B, 3), (:B, 5)], (2, 4), cperm())
```

`p_a` returns the classification of the resulting subsystem as a vector of
`(type, rank)` pairs (e.g. `[(:B, 6), 1]`) together with supporting data.


### Diagram automorphisms

For type `A` and `D` root systems, `diagram_automorphism(R, v, e)` returns the
root permutation `f` of the inner automorphism attached to subsystem `v`, where
`e` selects the folding: `e == 1` is unfolded, `e == 2` is the order‑2 folding.

```julia
f = diagram_automorphism(root_system(:D, 4), (:A, 3), 2)
```
## Public API

| Function | Purpose |
|---|---|
| `p_a(R, v, w, f)` | Anisotropic system of the quasimaximal subsystem specified by `v`, with anisotropic nodes `w` and automorphism `f`. |
| `diagram_automorphism(R, v, e)` | Root permutation `f` for the folded/und folded inner automorphism of a type-`A`/`D` subsystem. |
| `permutation_to_matrix(f, ro, m0)` | Matrix `F` acting on the ambient space for a root-index permutation `f`. |

    The underscore-prefixed helpers (_validate_v, _validate_w, _white_positions,
    simple_system, extend_basis, col_span_matrix) are re-exported for
    convenience/testing only.

## Descriptor reference

Inputs are validated by `_validate_v` / `_validate_w`. Besides lists of root indices or root vectors, the following forms are considered valid (per root system class):

- type A — `[(:A, m), nₘ]` or `[(:A, m), (:A, n−m−1)]`

- type B — `(k, nₖ)`, `[(:B, m), (:B, n−m)]`, or `[(:B, m), nₘ]`
- type C — `(k, nₖ)`, `[(:C, m), (:C, n−m)]`, `[(:C, m), nₘ]`, `[:A, n−1]`, `[:D, n]`
- type D — `(:A, n−1)`, `[(:D, m), (:D, n−m)]`, `[(:D, m), nₘ]`

`w` (anisotropic nodes) accepts `(d, r)`, `[(d₁,r₁),(d₂,r₂)]`, or `(x, r, d)` for
type `D`, plus explicit roots or root-index vectors.
## Running the tests
```bash
julia --project=. -e 'using Pkg; Pkg.test()'
```

or, directly:
```bash
julia --project=. test/runtests.jl
```

The suite covers the vector-space helpers, descriptor validation, the
diagram-automorphism permutations, the permutation-to-matrix conversion, and
regression expectations taken from the worked examples in `anisotropic_system.jl`

## Layout
```
src/
  vector_space_helpers.jl        # module/embedding helpers
  root_system_helpers.jl         # Cartan classification, diagram automorphisms
  validate_inpute_types.jl       # _validate_v / _validate_w
  descriptor_resolver.jl         # expand descriptors into explicit roots
  permutation_matrix.jl          # permutation → linear map
  anisotropic_system.jl             # top-level p_a entry point
```
