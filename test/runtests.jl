using Test
using Oscar
using MaximalSubgroups

# Load shared, test-only helpers. These live under test/ and are not part of the
# package itself, so they are `include()`d here (rather than `using`).
include("support/helpers.jl")

@testset "MaximalSubgroups.jl" begin

    # ---- vector_space_helpers.jl ----
    @testset "vector_space_helpers.jl" begin
        V = VectorSpace(QQ, 3)

        @testset "col_span_matrix" begin
            @test ncols(col_span_matrix(V, [])) == 0
            M = col_span_matrix(V, [[1, 0, 0], [0, 1, 0]])
            @test rank(M) == 2
        end

        @testset "extend_basis extracts a maximal independent subset" begin
            phi = [[1, 0, 0], [2, 0, 0], [0, 1, 0]]  # first two dependent
            @test length(extend_basis(V, phi)) == 2
        end

        @testset "simple_system returns the irreducible base" begin
            pos = [QQMatrix(1, 2, [1, 0]),        # a1
                QQMatrix(1, 2, [0, 1]),        # a2
                QQMatrix(1, 2, [1, 1])]        # a1 + a2
            @test length(simple_system(pos)) == 2   # only the two simple roots
        end
    end

    # ---- descriptor_resolver.jl ----
    @testset "descriptor_resolver.jl (helpers)" begin
        @testset "_white_positions(d, r, size)" begin
            @test _white_positions(2, 2, 5) == [2, 4]
            @test _white_positions(3, 1, 5) == [3]
            @test _white_positions(1, 3, 5) == [1, 2, 3]
            @test_throws ArgumentError _white_positions(3, 2, 4)  # d*r > size
        end
    end

    # ---- validate_inpute_types.jl ----
    @testset "validate_inpute_types.jl (_validate_v)" begin
        R6C = root_system(:C, 6)
        R5A = root_system(:A, 5)

        # valid descriptors per class
        @test _validate_v(R6C, (3, 3)) === nothing     # (k, nk)
        @test _validate_v(R6C, [:A, 5]) === nothing     # [:A, n-1] box inside C_6
        @test _validate_v(R6C, [:D, 6]) === nothing     # [:D, n]   box inside C_6
        @test _validate_v(R6C, [(:C, 2), (:C, 4)]) === nothing      # [(:C,m),(:C,n-m)]
        @test _validate_v(R5A, [(:A, 2), 2]) === nothing # [(:A,m),n_m] fills A_5  ((2+1)*2 = 6)

        # invalid shapes
        @test_throws ArgumentError _validate_v(R6C, [(:C, 3), (:C, 4)])  # 3+4 != 6
        @test_throws ArgumentError _validate_v(R6C, (:A, 3))              # :A needs n-1 = 5
        @test_throws ArgumentError _validate_v(R6C, [(:B, 2), (:B, 4)])   # wrong class
        @test_throws ArgumentError _validate_v(R5A, [(:A, 3), 2])         # (4)*2 != 6
    end

    @testset "validate_inpute_types.jl (_validate_w)" begin
        R6C = root_system(:C, 6)
        R6B = root_system(:B, 6)

        @test _validate_w(R6C, (2, 2)) === nothing  # (d, r)
        @test _validate_w(R6C, [(2, 2), (2, 1)]) === nothing  # C_m x C_{n-m}
        @test _validate_w(R6B, (3,)) === nothing  # type B single entry

        @test_throws ArgumentError _validate_w(R6C, (0, 2))  # d >= 1
    end

    # ---- diagram_automorphism.jl ----
    @testset "diagram_automorphism.jl" begin
        # A folded/reflected order-2 automorphism must still be a valid permutation.
        f = diagram_automorphism(root_system(:D, 4), (:A, 3), 2)
        @test f isa Oscar.PermGroupElem
        @test Oscar.degree(parent(f)) > 0

        f2 = diagram_automorphism(root_system(:A, 5), [(:A, 2), (:A, 2)], 1)
        @test f2 isa Oscar.PermGroupElem
        @test Oscar.degree(parent(f2)) > 0
    end

    # ---- permutation_matrix.jl ----
    @testset "permutation_matrix.jl" begin
        R = root_system(:A, 4)
        ro = [root(R, i).vec for i in 1:num_roots(R)]
        _, _, _, _, m0 = simple_root_embedding(R)   # m0: rows are the simple roots

        f = cperm([2, 1])                # transposition (1 2) of root indices
        F = permutation_to_matrix(f, ro, m0)

        deg = Oscar.degree(parent(f))
        @test F * transpose(ro[1] * m0) == transpose(ro[f(1)] * m0)   # f: 1 -> 2
        @test F * transpose(ro[2] * m0) == transpose(ro[f(2)] * m0)   # f: 2 -> 1
        @test abs(det(F)) == 1           # F preserves the metric
    end

    # ---- anisotropic_system.jl (reference expectations) ----
    # The expected classifications below are taken verbatim from the "should
    # return" comments in anisotropic_system.jl. If the installed Oscar version
    # reports a different shape, adjust the expected (type, rank) pairs.
    @testset "anisotropic_system.jl (reference expectations)" begin
        R = root_system(:B, 8)
        g, _, _, _, _ = anisotropic_system(R, [(:B, 3), (:B, 5)], (2, 4), cperm())
        @test (:B, 6) in _components(g)

        g, _, _, _, _ = anisotropic_system(R, [(:B, 4), 2], (3,), cperm())
        @test (:B, 6) in _components(g)
        @test (:A, 1) in _components(g)

        R = root_system(:C, 12)
        g, _, _, _, _ = anisotropic_system(R, (4, 3), (2, 2), cperm())
        @test (:A, 5) in _components(g)

        R = root_system(:C, 10)
        g, _, _, _, _ = anisotropic_system(R, [(:C, 4), (:C, 6)], [(2, 2), (2, 1)], cperm())
        @test (:A, 1) in _components(g)
        @test (:C, 4) in _components(g)

        R = root_system(:A, 23)
        v, w = [(:A, 7), 3], (2, 1)
        f = diagram_automorphism(R, v, 2)
        g, _, _, _, _ = anisotropic_system(R, v, w, f)
        @test (:A, 5) in _components(g)
        @test (:A, 11) in _components(g)

        R = root_system(:D, 30)
        v, w = [(:D, 20), (:D, 10)], ((4, 3), (4, 1))
        f = diagram_automorphism(R, v, 2)
        g, _, _, _, _ = anisotropic_system(R, v, w, f)
        @test (:D, 14) in _components(g)
        @test (:A, 3) in _components(g)
    end
end