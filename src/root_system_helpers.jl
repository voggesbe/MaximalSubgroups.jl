using Oscar
using Graphs

"""
    simple_system(pos::Vector{QQMatrix}) -> Vector{QQMatrix}

Base of the root system whose positive roots are `pos` (1×n integer rows in
simple-root coordinates): the roots that are not a sum of two positive roots.
"""
function simple_system(pos::Vector)
    key(r) = Tuple(Int(x) for x in r)
    S = Set(key(r) for r in pos)
    return [a for a in pos
                  if !any(b -> (key(a) .- key(b)) in S, pos)]
end

"""
    _root_space(d::Int) -> Tuple{Generic.FreeModule{QQFieldElem}, Hecke.QuadSpace, QQMatrix}

Build the vector space, quadratic space, and standard basis matrix of
dimension `d` used to embed a root system's simple roots.
"""
function _root_space(d::Int)
    V2 = VectorSpace(QQ, d)
    V1 = quadratic_space(QQ, d)
    E = identity_matrix(QQ, d)
    return V2, V1, E
end


"""
    simple_root_embedding(R::RootSystem) -> Tuple{Hecke.QuadSpace, Generic.FreeModule{QQFieldElem}, QQMatrix}

Embed the simple roots of the irreducible root system `R` into a concrete
coordinate vector space. Returns `(V1, V2, m, E)`, where the columns of `m`
are the images of the simple roots and E is the matrix of the standard basis.
"""
function simple_root_embedding(R::RootSystem)
    components = root_system_type(R)
    length(components) == 1 ||
        error("simple_root_embedding only supports irreducible root systems (got $(length(components)) components)")
    S::Symbol, l::Int = components[1]

    local V1, V2, E, m_basis, m_simple_roots

    if S == :A
        V2, V1, E = _root_space(l + 1)
        cols = [E[:, i] - E[:, i+1] for i in 1:l]
        m_simple_roots = matrix([to_elem(V2, c) for c in cols])
        m1 = append!([to_elem(V2, c) for c in cols], [to_elem(V2, (E[:, l+1]))])
        m_basis = transpose(matrix(m1)) #vectors for simple roots
    elseif S == :B
        V2, V1, E = _root_space(l)
        cols = [[E[:, i] - E[:, i+1] for i in 1:(l-1)]; [E[:, l]]]
        m_simple_roots = matrix([to_elem(V2, c) for c in cols])
        m_basis = transpose(m_simple_roots)
    elseif S == :C
        V2, V1, E = _root_space(l)
        cols = [[E[:, i] - E[:, i+1] for i in 1:(l-1)]; [2 * E[:, l]]]
        m_simple_roots = matrix([to_elem(V2, c) for c in cols])
        m_basis = transpose(m_simple_roots)

    elseif S == :D
        V2, V1, E = _root_space(l)
        cols = [[E[:, i] - E[:, i+1] for i in 1:(l-1)]; [E[:, l-1] + E[:, l]]]
        m_simple_roots = matrix([to_elem(V2, c) for c in cols])
        m_basis = transpose(matrix([to_elem(V2, c) for c in cols]))

    elseif S == :E
        l == 6 || error("simple_root_embedding currently only supports E6, not E$l")
        V2, V1, E = _root_space(9)
        base = [to_elem(V2, E[:, i] - E[:, i+1]) for i in 2:8]
        special = V2(QQFieldElem[1//3, -2//3, 1//3, -2//3, 1//3, 1//3, -2//3, 1//3, 1//3])
        ordered = [base[7], base[1], base[6], special, base[3], base[4]]
        extra = E[:, [1, 4, 7]]
        m_simple_roots = matrix(ordered)
        m_basis = hcat(transpose(m_simple_roots), extra)

    else
        error("simple_root_embedding: unsupported root system type $S$l")
    end

    return V1, V2, E, m_basis, m_simple_roots
end

"""
    cartan_matrix_of_roots(roots::Vector{QQMatrix}, m::QQMatrix, V::Generic.FreeModule{QQFieldElem}) -> Tuple{QQMatrix, Vector{QQMatrix}}

Build the Cartan-type matrix for a list of (simple) root coordinate
vectors `roots`, embedded via `m` into `V`. Also returns the embedded
root vectors (as 1×n matrices) for reuse by callers.
"""
function cartan_matrix_of_roots(roots::Vector{<:QQMatrix}, m::QQMatrix, V::Generic.FreeModule{QQFieldElem})
    simple_roots_vector = [matrix([to_elem(V, r * m)]) for r in roots]
    k = length(roots)
    c_matrix = diagonal_matrix(QQ(2), k)
    for i in 1:k, j in 1:k
        if i != j
            c_matrix[i, j] = 2 * (simple_roots_vector[j]*transpose(simple_roots_vector[i]))[1] / (simple_roots_vector[i]*transpose(simple_roots_vector[i]))[1]
        end
    end
    return c_matrix, simple_roots_vector
end

"""
    split_into_irreducibles(simple_roots::Vector{QQMatrix}, embedding_matrix::QQMatrix, V::Generic.FreeModule{QQFieldElem}) -> Tuple{Vector{Vector{QQMatrix}}, Vector{QQMatrix}}

Given a list of simple roots `simple_roots`, split into irreducible components.
Returns `(irred_comps, irred_cartans)`.
"""
function split_into_irreducibles(simple_roots::Vector{<:QQMatrix}, embedding_matrix::QQMatrix, V::Generic.FreeModule{QQFieldElem})
    C, _ = cartan_matrix_of_roots(simple_roots, embedding_matrix, V)
    k = length(simple_roots)
    A = Array{Int}(undef, k, k) # adjacency matrix
    for i in 1:k, j in 1:k
        A[i, j] = i == j ? 0 : Int(numerator(C[i, j]*C[j, i]))
    end
    # find the irreducible components in the root system with the help of A
    g = SimpleGraph(A)
    comp = Graphs.connected_components(g)
    irred_comps = [[simple_roots[idx] for idx in c] for c in comp]
    irred_cartans = [cartan_matrix_of_roots(c, embedding_matrix, V)[1] for c in irred_comps]
    return irred_comps, irred_cartans
end

"""
    classify_cartan_component(C::QQMatrix, roots::Vector{QQMatrix}, embedding_matrix::QQMatrix, V, types::Vector{Symbol}) -> Tuple{Symbol, Int}

Identify the Cartan type and rank of a single irreducible Cartan matrix
`C`, coming from the simple roots `roots`. `types` is read-only.
"""
function classify_cartan_component(
    C::QQMatrix,
    roots::Vector{<:QQMatrix},
    embedding_matrix::QQMatrix,
    V::Generic.FreeModule{QQFieldElem},
    types::Vector{Symbol},
)::Tuple{Symbol,Int}
    rk = rank(C)
    JNF1 = jordan_normal_form(C)[1]
    Ma = matrix_space(QQ, rk, rk)
    j = 1
    JNF2 = jordan_normal_form(Ma(cartan_matrix(:A, rk)))[1]
    # find the root system via the JNF of the cartan matrix
    while JNF2 != JNF1 && j < 7
        j += 1
        t = types[j]
        if (t == :E && rk in (6, 7, 8)) || (t == :F && rk == 4) || (t == :G && rk == 2)
            JNF2 = jordan_normal_form(Ma(cartan_matrix(t, rk)))[1]
        elseif t == :D && rk < 4
            JNF2 = jordan_normal_form(Ma(cartan_matrix(:A, rk)))[1]
        elseif t in (:A, :B, :C, :D)
            JNF2 = jordan_normal_form(Ma(cartan_matrix(t, rk)))[1]
        end
    end
    if JNF1 != JNF2
        error("component with Cartan matrix $cartan_matrix does not match any known root system type")
    end

    resolved_type::Symbol = types[j]
    # check if type is B or C
    if resolved_type in (:B, :C) && rk != 2
        l = findfirst(idx -> C[idx[1], idx[2]] == -2, [(i, j1) for i in 1:rk, j1 in 1:rk])
        i0, j0 = l[1], l[2]
        _, v_sR = cartan_matrix_of_roots(roots, embedding_matrix, V)
        v_other = deleteat!(copy(v_sR), sort([i0, j0]))
        sqlen(v) = (v*transpose(v))[1]
        l1, l2, l3 = sqlen(v_sR[i0]), sqlen(v_sR[j0]), sqlen(v_other[1])
        if l1 == l3
            resolved_type = l2 < l1 ? :B : :C
        elseif l2 == l3
            resolved_type = l1 < l2 ? :B : :C
        end
    end
    return resolved_type, rk
end


function find_root_system_type(v, m0, V2, V0)
    s_R = extend_basis(V0, v) # find the simple roots
    irred_comps, irred_cartans = split_into_irreducibles(s_R, m0, V2)

    # we can check what root system it is by checking for each indecomposable factor
    root_system_G = []
    types = [:A, :B, :C, :D, :E, :F, :G]
    for i = 1:length(irred_cartans)
        resolved_type, rk=classify_cartan_component(irred_cartans[i], irred_comps[i], m0, V2, types)
        ro = [root_system_G[i][1] for i = 1:length(root_system_G)]
        #if we already found this root system, add +1 to the number describing how many we have
        if (resolved_type, rk) in ro
            j = findfirst(==((resolved_type, rk)), ro)
            root_system_G[j][2] += 1
        else
            append!(root_system_G, [[(resolved_type, rk), 1]])
        end
    end
    return root_system_G, s_R
end

#helper functions to get (i,m_i) for the subsystems A_i^(m_i) and (j,n-1-j) for A_j x A_(n-1-j)
function subsystem(R::RootSystem)
    S, n = root_system_type(R)[1]
    if S == :A
        s1 = []
        s2 = []
        div = divisors(n + 1)
        for i in div
            if (n+1)/i >= 3 && i-1 > 0
                append!(s1, [[(:A, i-1), Int((n+1)/i)]])
            end
        end
        s2 = [[(:A, j), (:A, n-1-j)] for j = 0:Int(floor((n-1)/2))]
    end
    return s1, s2
end


"""
    diagram_automorphism(R::RootSystem, v, e::Int)

Root permutation `f` of the inner automorphism attached to the subsystem `v`,
where `e` selects the diagram folding: `e == 1` unfolded, `e == 2` the order‑2
automorphism. Implemented for `R` of type `A` and `D`.
"""
function diagram_automorphism(R::RootSystem, v, e::Int)
    S, n = root_system_type(R)[1]
    ro = [root(R, i).vec for i = 1:num_roots(R)]

    f = S == :A ? _diagram_automorphism_A(v, n, e) :
        S == :D ? _diagram_automorphism_D(v, n, ro, R, e) :
        throw(ArgumentError("subindex: only types A and D are implemented"))

    f === nothing &&
        throw(ArgumentError("subindex: no permutation for v = $(repr(v)) (e = $e)"))
    return f
end

# ---- type A ---------------------------------------------------------------
function _diagram_automorphism_A(v, n, e::Int)
    if v[2] isa Int                                          # box  A_m^{nm}  in A_n
        m = v[1][2]
        (m + 1) * v[2] == n + 1 ||
            throw(ArgumentError("subindex: (:A, $m) box does not fill A_$n"))
        if e == 1                                           # unfolded
            return cperm([[(j - 1) * (m + 1) + k for j = 1:v[2]] for k = 1:m])
        elseif e == 2 #folded
            v0 = [[(j-1)*(v[1][2]+1)+k for j = 1:v[2]] for k = 1:v[1][2]]
            v1 = [[v0[k], reverse(v0[length(v0)-k+1])] for k=1:Int(floor(v[1][2]/2))]
            v2 = [reduce(vcat, v1[i]) for i = 1:length(v1)]
            if v[1][2] % 2 == 1
                v3 = [Int((v[1][2]+1)/2)+i*(v[1][2]+1) for i = 0:(v[2]-1)]
                v2 = vcat(v2, [v3])
            end
            return cperm(v2)
        end
    elseif v[2] isa Tuple                                   # product [(:A_m),(:A,n-m-1)]
        m, k = v[1][2], v[2][2]
        f1 = [[i, m - i + 1] for i = 1:fld(m, 2)]
        f2 = [[m + 1 + i, n - i + 1] for i = 1:fld(k, 2)]
        return cperm(vcat(f1, f2))
    end
    return nothing
end

# ---- type D ---------------------------------------------------------------
function _diagram_automorphism_D(v, n, ro, R, e::Int)
    _, _, E, m0 = simple_root_embedding(R)
    antipode(r) = findall(==(-r), ro)[1]                     # index of the root −r

    vtype = v[1] isa Tuple ? v[1][1] : v[1]                  # (:A,·) | (:D,·) | :A | :D

    if vtype == :A                                          # subsystem (:A, n-1)
        if iseven(n)                                        # A_{n-1}, n-1 odd
            return cperm([[i, n - i] for i = 1:fld(n-1, 2)])
        elseif e == 1                                       # n odd, unfolded
            return cperm([n - 1, n])
        else                                                # n odd, folded
            return cperm(vcat([[i, n - i] for i = 1:fld(n-1, 2)], [[n, antipode(ro[n])]]))
        end
    elseif length(v) == 2 && v[2] isa Tuple                 # product [(:D_m),(:D,n-m)]
        j1 = antipode(ro[Int(length(ro) / 2)])
        return cperm([j1, 1], [n, n - 1])
    elseif length(v) == 2 && v[2] isa Int                   # box  [(:D_m),nm]
        m, nm = v[1][2], v[2]
        image_idx(i) = findall(==(transpose(matrix((E[i*m-1, :] + E[i*m, :]) * inv(m0)))), ro)[1]
        f1 = [[p + m * i for i = 0:(nm-1)] for p = 1:(m-1)]
        f2 = [image_idx(i) for i = 1:nm]
        if isodd(e)                                         # unfolded
            return cperm(vcat(f1, [f2]))
        else                                                # folded
            f1[end] = vcat(f1[end], f2)
            return cperm(f1)
        end
    end
    return nothing
end