#!/usr/env/env julia
# ---------------------------------------------------------------------------
# examples/example.jl
#
# Runnable worked examples for MaximalSubgroups.jl.
#
#     julia --project=. examples/example.jl
#
# Each block calls anisotropic_system (or one of the helpers) on a real Cartan type and
# checks the result against the value documented in
# src/anisotropic_system.jl.
# ---------------------------------------------------------------------------

using Oscar
using Test
using MaximalSubgroups

# anisotropic_system reports the resolved subsystem as a list of
#        [((type, rank), multiplicity)]
# tuples.  This helper flattens it to the plain list of (type, rank) pairs so
# an example can simply write `@test (:B, 6) in components(g)`.
components(g) = [pairing[1] for pairing in g]

banner() = println(repeat("=", 72))

banner()
println("  MaximalSubgroups.jl  -  worked examples")
println("  run:  julia --project=. examples/example.jl")
banner()

# ---------------------------------------------------------------------------
# 1. Type B  -  a (B_m, B_{n-m}) quasimaximal subsystem.
#    Documented in src/anisotropic_system.jl as returning [(:B, 6), 1].
# ---------------------------------------------------------------------------
println("\n[1] Type B     R = root_system(:B, 8)     v = [(:B, 3), (:B, 5)]     w = (2, 4)")

R = root_system(:B, 8)
g, I, B, s_R, F = anisotropic_system(R, [(:B, 3), (:B, 5)], (2, 4), cperm())
println("    resolved subsystem : ", components(g))
@test (:B, 6) in components(g)

# ---------------------------------------------------------------------------
# 2. Type C  -  cyclic (k, n_k) subsystem with the (d, r) anisotropic pattern.
#    Documented as returning [(:A, 5), 2].
# ---------------------------------------------------------------------------
println("\n[2] Type C     R = root_system(:C, 12)     v = (4, 3)     w = (2, 2)")

R = root_system(:C, 12)
g, _, _, _, _ = anisotropic_system(R, (4, 3), (2, 2), cperm())
println("    resolved subsystem : ", components(g))
@test (:A, 5) in components(g)

# ---------------------------------------------------------------------------
# 3. Type D  -  a (D_m, D_{n-m}) subsystem, resolved by the order-2
#    diagram automorphism f = diagram_automorphism(R, v, 2).
#    Documented as returning [[(:D, 14), 1], [(:A, 3), 4]].
# ---------------------------------------------------------------------------
println("\n[3] Type D     R = root_system(:D, 30)     v = [(:D, 20), (:D, 10)]")

R = root_system(:D, 30)
v = [(:D, 20), (:D, 10)]
w = ((4, 3), (4, 1))
f = diagram_automorphism(R, v, 2)
g, I, B, s_R, _ = anisotropic_system(R, v, w, f)
println("    resolved subsystem : ", components(g))
@test (:D, 14) in components(g)
@test (:A, 3) in components(g)

# ---------------------------------------------------------------------------
# 4. diagram_automorphism standalone.
# ---------------------------------------------------------------------------
println("\n[4] diagram_automorphism    R = root_system(:D, 4)    v = (:A, 3)    e = 2")

f = diagram_automorphism(root_system(:D, 4), (:A, 3), 2)
println("    f = ", f)

# ---------------------------------------------------------------------------
# 5. permutation_to_matrix standalone.
# ---------------------------------------------------------------------------
println("\n[5] permutation_to_matrix    R = root_system(:A, 3)")

R = root_system(:A, 3)
ro = [root(R, i).vec for i in 1:num_roots(R)]
_, _, _, _, m0 = simple_root_embedding(R)
f = cperm([1, 3])                          # fold A_3's diagram
F = permutation_to_matrix(f, ro, m0)
println("    F = ", F)
@test abs(det(F)) == 1

# ---------------------------------------------------------------------------
banner()
println("  All examples passed")