using Oscar

# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

"""
    _normalize_roots(x) -> Vector{QQMatrix}
 
Flatten an arbitrarily nested collection of roots (1×n `QQMatrix`, or root
objects with a `.vec` field) into a flat `Vector{QQMatrix}`.
"""
function _normalize_roots(x)::Vector{QQMatrix}
    out = QQMatrix[]
    _collect_roots!(out, x)
    return out
end

_collect_roots!(out, r::QQMatrix) = push!(out, r)
_collect_roots!(out, r::RootSpaceElem) = push!(out, r.vec)
function _collect_roots!(out, xs::Union{AbstractVector,Tuple})
    for x in xs
        _collect_roots!(out, x)
    end
    return out
end
_collect_roots!(out, x) =
    throw(ArgumentError("p_a: cannot interpret $(typeof(x)) as a root (unresolved descriptor?)"))

# remove the entries of `v` at positions `x` (duplicates in `x` are allowed)
_drop(v, x) = deleteat!(copy(v), sort!(unique(x)))

# ---------------------------------------------------------------------------
# type A
# ---------------------------------------------------------------------------

function _resolve_A(v, w, f, n_rank, ro)
    s = nothing
    if v isa Tuple || v isa Vector
        # this means v can be:
        # [(:A,m), n_m]
        # [(:A,m),(:A,n-m-1)]
        if v[1] isa Tuple && v[2] isa Tuple            # [(:A,m),(:A,n-m-1)]
            v2 = vcat(ro[1:v[1][2]], ro[(v[1][2]+2):(v[1][2]+v[2][2]+1)])
            s = (v[1][2], v[2][2])
        elseif v[1] isa Tuple && v[2] isa Int                            # [(:A,m),n_m]
            v2=QQMatrix[]
            for i = 1:v[2]
                append!(v2, ro[((i-1)*(v[1][2]+1)+1):(i*(v[1][2]+1)-1)])
            end
            s = (v[1][2], v[2])
        else
            throw(ArgumentError("p_a: unrecognised type-A descriptor v"))
        end
        v = v2
    end
    # otherwise v is already an explicit list of roots and is left untouched

    if w isa Tuple # For type A, we allow w = (d,r) if v = [(:A,m),n_m]
        # or w = ((d1,r1),(dr,r2)) if v = [(:A,m),(:A,n-m-1)]
        s === nothing &&
            throw(ArgumentError("p_a: tuple w requires a tuple v for type A"))
        if w[1] isa Tuple                               # w = ((d1,r1),(d2,r2))
            d1, r1 = w[1]
            d2, r2 = w[2]
            x = vcat([i*d1 for i = 1:r1], [i*d2 + s[1] for i = 1:r2])
        else                                            # w = (d, r)
            d, r = w
            H = sub(parent(f), [f])[1]
            o = orbit(H, n_rank)
            if length(o) == s[2]                     # no folding
                x = reduce(vcat, [[i*d + j*s[1] for i = 1:r] for j = 0:(s[2]-1)])
            elseif length(o) == 2*s[2]                  # folding
                x1 = reduce(vcat, [[i*d + j*s[1] for i = 1:r] for j = 0:(s[2]-1)])
                x2 = reduce(vcat, [[((1+j)*s[1] - i*d + 1) for i = 1:r] for j = 0:(s[2]-1)])
                x = vcat(x1, x2)
            else
                throw(ArgumentError("p_a: orbit length $(length(o)) incompatible with descriptor (d,r)"))
            end
        end
        w = _drop(v, x)                 # operates on the resolved v
    end
    return v, w
end
# ---------------------------------------------------------------------------
# type B
# ---------------------------------------------------------------------------
function _resolve_B(v, w, n_rank, ro)
    c = nothing                                          # groups of root indices, built from v = (k, nk)
    if v isa Tuple # v=(k, nk)  
        k, nk = v
        neg_first(m) = findfirst(==(-sum(ro[(m*k+1):n_rank])), ro) # closing long root of copy m
        num_list = Int[]
        for m = 0:(nk-2)
            append!(num_list, [m*k + i for i = 1:(k-1)])
            append!(num_list, [neg_first(m)])
        end
        append!(num_list, [i for i in ((nk-1)*k+1):n_rank])
        v = [ro[i] for i in num_list]

        num_tup = Int[]
        for m = 0:(nk-2)
            append!(num_tup, [neg_first(m)])
        end
        append!(num_tup, n_rank)
        num_tup_2 = Vector{Int}[]
        for r = 1:(k-1)
            push!(num_tup_2, [m*k + r for m = 0:(nk-2)])
            push!(num_tup_2, [n_rank - r])
        end
        c = vcat(Vector{Int}[num_tup], num_tup_2)
        f = cperm([reduce(vcat, c[i]) for i = 1:length(c)])
    end
    if w isa Tuple # w is not yet a list of roots  
        c === nothing &&
            throw(ArgumentError("p_a: tuple w requires a tuple v = (k, nk) for type B"))
        i = w[1]
        w = [ro[c[j]] for j = 1:i]            # list of roots, no flattening
    end
    return v, w
end

# ---------------------------------------------------------------------------
# type C
# ---------------------------------------------------------------------------

function _resolve_C(v, w, n_rank, ro)
    if v isa Tuple && length(v) == 2          # [(:C,m),n_m]
        k, nk = v
        neg_first(m) = findfirst(==(-(2*sum(ro[(m*k+1):(n_rank-1)]) + ro[n_rank])), ro)
        num_list = Int[]
        for m = 0:(nk-2)
            append!(num_list, [m*k + r for r = 1:(k-1)])
            append!(num_list, [neg_first(m)])
        end
        append!(num_list, [n_rank - r for r in 0:(k-1)])
        v = [ro[i] for i in num_list]

        num_tup = Int[]
        for m = 0:(nk-2)
            append!(num_tup, [neg_first(m)])
        end
        append!(num_tup, n_rank)
        num_tup_2 = Vector{Int}[]
        for r = 1:(k-1)
            push!(num_tup_2, vcat([m*k + r for m = 0:(nk-2)], [n_rank-(k-r)]))
        end
        c = vcat(Vector{Int}[num_tup], num_tup_2)
        f = cperm([reduce(vcat, c[i]) for i = 1:length(c)])

        if w isa Tuple                          # w = (d, r)
            d, r = w
            if k == r*d
                w = [ro[c[j*d+i]] for j in 0:(r-1) for i in 2:d]
            else
                w = vcat([ro[c[i]] for i in 1:(k-r*d)],
                    [ro[c[k-m*d+i]] for m in 1:r for i in 2:d])
            end
        end
    elseif isempty(v) == 0                       # [(:A,n-1)] box
        v = [ro[i] for i in 1:(n_rank-1)]
        if w isa Tuple
            d, r = w
            num_tup_2 = Vector{Int}[]
            for j in 1::((n_rank-1)/2)  # pairs (j, n-j) with j < n-j
                push!(num_tup_2, [j, n_rank - j])
            end
            c = num_tup_2
            f = cperm([reduce(vcat, c[i]) for i = 1:length(c)])
            x = vcat([i*d for i in 1:r], [n_rank - i*d for i in 1:r])
            w = _drop(v, x)
        end
    end
    return v, w, f
end

# ---------------------------------------------------------------------------
# type D
# ---------------------------------------------------------------------------

function _resolve_D(v, w, f, n_rank, ro, E, m0)
    v isa Tuple || return v, w                           # explicit roots: nothing to resolve

    if v[1][1] == :A                                     # subsystem (:A, n-1)
        v2 = ro[1:v[1][2]]
        if w isa Tuple
            d, r = w
            x = vcat([i*d for i in 1:r], [n_rank - i*d for i in 1:r])
            w = _drop(v2, x)
        end
        v = v2

    elseif v[1][1] == :D && v[2] isa Tuple               # [(:D,m),(:D,n-m)]
        neg = (-E[:, 1] - E[:, 2]) * inv(m0)    # 1×n QQMatrix
        v2 = vcat(transpose(matrix(neg)), ro[1:(v[1][2]-1)], ro[(v[1][2]+1):n_rank])
        if w isa Tuple
            d1, r1 = w[1]
            d2, r2 = w[2]
            x1 = [v[1][2] - i*d1 + 1 for i in 1:r1]
            ol = Set(orbit(parent(f), sub(parent(f), [f])[1], n_rank))
            if d1*r1 + 1 == v[1][2] && (n_rank - 1 in ol)
                x1 = (vcat(x1, [1, 2]))
            end
            x2 = [v[1][2] + i*d2 for i in 1:r2]
            if d2*r2 + 1 == n_rank - v[1][2] && (n_rank - 1 in ol)
                x2 = vcat(x2, [n_rank, n_rank-1])
            end
            w = deleteat!(copy(v2), sort(vcat(x1, x2)))
        end
        v = v2

    elseif v[1][1] == :D && v[2] isa Int         # [(:D,m),n_m]
        v2 = QQMatrix[]
        for i in 1:v[2]
            a = v[1][2]*(i-1)
            z = transpose(E[:, a+v[1][2]-1] + E[:, a+v[1][2]]) * inv(m0)
            append!(v2, ro[(a+1):(a+v[1][2]-1)])
            push!(v2, z)                                 # z is a single 1×n matrix
        end
        if w isa Tuple
            d, r = w
            x = reduce(vcat, [[i*d + v[1][2]*j for i in 1:r] for j in 0:(v[2]-1)])
            if d*r + 1 == v[1][2]
                x = vcat(x, reduce(vcat, [[v[1][2]*j - 1, v[1][2]*j] for j in 1:v[2]]))
            end
            w = _drop(v2, x)
        end
        v = v2
    end
    return v, w
end

# ---------------------------------------------------------------------------
# entry point
# ---------------------------------------------------------------------------

"""
    _resoleve_vw(R::RootSystem, v::VInput, w::WInput, f::PermGroupElem)

    Resolve the (possibly abbreviated) descriptors `v` (quasimaximal subsystem) and
`w` (anisotropic / black roots) into actual lists of roots of `R`, returning the
(perhaps rebuilt) automorphism `f`.

Input forms are documented on [`p_a`](@ref) and validated by `_validate_v` /
`_validate_w`. `f` is rebuilt from `v` for the cyclic (`B`, `C`) and box (`C`)
automorphisms.
"""
function _resolve_vw(R::RootSystem, v, w, f, E, m0)
    S = root_system_type(R)[1][1]
    n_rank = num_simple_roots(R)
    ro = [root(R, i).vec for i = 1:num_roots(R)]

    # explicit root indices -> roots
    v isa Vector{Int} && (v = ro[v])
    w isa Vector{Int} && (w = ro[w])

    if S == :A
        v, w = _resolve_A(v, w, f, n_rank, ro)
    elseif S == :B
        v, w = _resolve_B(v, w, n_rank, ro)
    elseif S == :C
        v, w, f = _resolve_C(v, w, n_rank, ro)
    elseif S == :D
        v, w = _resolve_D(v, w, f, n_rank, ro, E, m0)
    end
    return _normalize_roots(v), _normalize_roots(w), f
end