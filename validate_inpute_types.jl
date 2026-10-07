# v: descriptor list OR explicit roots, reshaped in-body to indices/roots
const VInput = Union{
    Vector{RootSystem},                                    # [R[1],R[3],...]
    Vector{Int},                                           # explicit indices
    Vector{Any},
    Tuple{Tuple{Symbol,Int},Int},                          # [(:A,m), n_m]
    Tuple{Tuple{Symbol,Int},Tuple{Symbol,Int}},            # [(:A,m),(:A,n-m-1)]
    Tuple{Tuple{Symbol,Int},Tuple{Symbol,Int}},            # [(:D,m),(:D,n-m)]
    Tuple{Tuple{Symbol,Int},Int},                          # [(:D,m),n_m]
    Tuple{Int,Int},                                        # (k, nk)  type B/C
    Vector{Int},                                           # (k, nk) box / empty (type C)
    Vector{Tuple{Symbol,Int}}
}

# w: anisotropic (black) nodes OR their descriptors
const WInput = Union{
    Vector{RootSystem},                                    # explicit roots / []
    Vector{Int},                                           # indices
    Tuple{Int,Int},                                      # (d, r)
    Tuple{Tuple{Int,Int},Tuple{Int,Int}},                # ((d1,r1),(d2,r2))
    Tuple{Int,Int,Int},                                  # (x, r, d)  type D
}

"""
    _validate_v(R::RootSystem, v)

Validate the input descriptor `v` for [`p_a`](@ref).

`v` may be:

- a single [`RootSystem`](@ref) root in `R`
- a `Vector{RootSystem}` of explicit roots
- a descriptor tuple whose exact shape depends on the class `S` of `R`:
  - type `A`: `[(:A, m), n_m]` or `[(:A, m), (:A, n-m-1)]`
  - type `B`/`C`: `(k, nk)` or a vector of root indices
  - type `D`: `(:A, n-1)` or `(:D, m) × (:D, n-m)` or `(:D, m)^(n_m)`

Throws `ArgumentError` when the shape doesn't fit the class, or when an
explicit root isn't in `R`.
"""
function _validate_v(R::RootSystem, v::VInput)
    S, l = root_system_type(R)[1]
    n_rank = num_simple_roots(R)
    n_roots = num_roots(R)

    S == :A || S == :B || S == :C || S == :D || S == :E ||
        throw(ArgumentError("p_a: unsupported root system type $S"))

    # ---- type A -------------------------------------------------------------
    if S == :A
        if v isa RootSystem
            return v in roots(R) ? nothing : throw(ArgumentError("p_a: root not in R"))
        elseif v isa Vector{<:RootSystem}
            for r in v
                r in roots(R) || throw(ArgumentError("p_a: root not in R"))
            end
            return
        elseif v isa Tuple || v isa Vector
            # descriptor form: [(:X,m), n_m] or [(:X,m),(:A,n-m-1)]
            typeof(v[1]) <: Tuple || throw(ArgumentError("p_a: type-A descriptor must start with (:A, m)"))
            v[1][1] == :A || throw(ArgumentError("p_a: type-A subsystem must be of the form (:A, m)"))
            m = v[1][2]
            2 <= m <= n_rank || throw(ArgumentError("p_a: type-A m=$m out of range 2:$n_rank"))
            if typeof(v[2]) <: Tuple       # (:A,m) × (:A,n-m-1)
                v[2][1] == :A || throw(ArgumentError("p_a: second descriptor must be (:A, n-m-1)"))
                m2 = v[2][2]
                m + m2 + 1 == n_rank || throw(ArgumentError("p_a: (m,m2) do not partition A_$n_rank"))
            elseif v[2] isa Int           # (:A,m)^{n_m}
                (m + 1) * v[2] == n_rank + 1 ||
                    throw(ArgumentError("p_a: (:A,$m) repeated $(v[2])× does not fill A_$n_rank"))
            else
                throw(ArgumentError("p_a: type-A descriptor second element must be Int or (:A, ·)"))
            end
            return
        end
        throw(ArgumentError("p_a: type-A v must be a root, a Vector{Root}, or a descriptor tuple"))

        # ---- type B / C / D -----------------------------------------------------
    elseif S == :B || S == :C
        if v isa Tuple
            typeof(v) <: Tuple{Int,Int} || throw(ArgumentError("p_a: type-$(S) v must be (k, nk)"))
            k, nk = v
            1 <= k <= n_rank || throw(ArgumentError("p_a: type-$(S) k=$k out of range"))
            nk >= 1 || throw(ArgumentError("p_a: type-$(S) nk=$nk must be ≥ 1"))
            return
        elseif v isa Vector
            isempty(v) && return   # type-C empty ([:A, n-1])
            all(x -> x isa Int && 1 <= x <= n_roots, v) ||
                throw(ArgumentError("p_a: type-$(S) integer vector must hold valid root indices"))
            return
        elseif v isa RootSystem
            return v in roots(R) ? nothing : throw(ArgumentError("p_a: root not in R"))
        end
        throw(ArgumentError("p_a: type-$(S) v must be (k, nk), an index vector, or a root"))

        # ---- type D -------------------------------------------------------------
    elseif S == :D
        if v isa Tuple
            typeof(v[1]) <: Tuple || throw(ArgumentError("p_a: type-D descriptor must start with a (:…, m)"))
            if v[1][1] == :A             # (:A, m) with n-1 roots
                m = v[1][2]
                m == n_rank - 1 || throw(ArgumentError("p_a: type-D (:A, m) needs m = n_rank-1"))
            elseif v[1][1] == :D        # (:D,m)×(:D,n-m) or (:D,m)^{n_m}
                m = v[1][2]
                3 <= m <= n_rank || throw(ArgumentError("p_a: type-D m=$m out of range 3:$n_rank"))
                if typeof(v[2]) <: Tuple  # (:D,m) × (:D,n-m)
                    v[2][1] == :D || throw(ArgumentError("p_a: type-D second descriptor must be (:D, ·)"))
                    m2 = v[2][2]
                    m + m2 == n_rank || throw(ArgumentError("p_a: m+m2=$(m+m2) must equal n_rank=$n_rank"))
                elseif v[2] isa Int     # (:D,m)^{n_m}
                    (m + 1) * v[2] == n_rank ||
                        throw(ArgumentError("p_a: (:D,$m) repeated $(v[2])× must fill D_$n_rank"))
                else
                    throw(ArgumentError("p_a: type-D second descriptor must be Int or (:D, ·)"))
                end
            else
                throw(ArgumentError("p_a: type-D first descriptor must be :A or :D"))
            end
            return
        elseif v isa Vector || v isa RootSystem
            return   # explicit roots
        end
        throw(ArgumentError("p_a: type-D v must be a descriptor tuple, explicit roots, or empty vector"))

        # ---- type E (only E6 supported) ----------------------------------------
    elseif S == :E
        if l == 6
            if v isa RootSystem
                return v in roots(R) ? nothing : throw(ArgumentError("p_a: root not in R"))
            elseif v isa Vector{<:RootSystem}
                for r in v
                    r in roots(R) || throw(ArgumentError("p_a: root not in R"))
                end
                return
            end
            throw(ArgumentError("p_a: type-E v must be a root or Vector{Root}"))
        end
        throw(ArgumentError("p_a: only E6 embedding is implemented"))
    end
end

"""
    _validate_w(R::RootSystem, w, v)

Validate the anisotropic (black) node descriptor `w` for [`p_a`](@ref).

`w` may be:

- a single [`RootSystem`](@ref) root in `R`
- a `Vector{RootSystem}` of explicit anisotropic roots
- a descriptor tuple, whose form depends on the class of `R`:
  - `(d, r)` — the anisotropic pattern for type `A`/`B`/`C` (or a type-`C` box)
  - `((d1, r1), (d2, r2))` — two patterns, used for the folded type `A` and `D × D` cases
  - `(x, r, d)` — the type-`D` pattern with `x ∈ {1, 2}`

All `d` and `r` values must be `≥ 1`, and `x` must be `1` or `2`.
Explicit roots must belong to `R`. Throws `ArgumentError` otherwise.
"""
function _validate_w(R::RootSystem, w)

    # any explicit-root vector is fine
    if w isa RootSystem
        return w in roots(R) ? nothing : throw(ArgumentError("p_a: anisotropic root not in R"))
    elseif w isa Vector{<:RootSystem}
        for r in w
            r in roots(R) || throw(ArgumentError("p_a: anisotropic root not in R"))
        end
        return
    end

    # descriptor tuples: shapes depend on the root-system class
    if w isa Tuple
        # (d, r) — A/B/C, or (:A,n-1) box
        if w isa Tuple{Int,Int}
            return (w[1] >= 1 && w[2] >= 1) ||
                throw(ArgumentError("p_a: (d, r) descriptors must be ≥ 1"))
            # ((d1,r1),(d2,r2)) — A (folded) or D × D
        elseif w isa Tuple{Tuple{Int,Int},Tuple{Int,Int}}
            for (d, r) in w
                (d >= 1 && r >= 1) || throw(ArgumentError("p_a: ((d,r),(d,r)) entries must be ≥ 1"))
            end
            return
            # (x, r, d) — type D
        elseif w isa Tuple{Int,Int,Int}
            return (w[1] in (1, 2) && w[2] >= 1 && w[3] >= 1) ||
                throw(ArgumentError("p_a: (x, r, d) for D needs x ∈ {1,2}, r,d ≥ 1"))
        end
    end

    throw(ArgumentError("p_a: w must be a root, explicit roots, or a descriptor tuple (d,r) / ((d,r),(d,r)) / (x,r,d)"))
end