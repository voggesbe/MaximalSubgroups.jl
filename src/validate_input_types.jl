# v: descriptor list OR explicit roots, reshaped in-body to indices/roots
const VInput = Union{
    Vector{QQMatrix},                                  # [R[1], R[3], ...] explicit roots
    Vector{Int},                                        # explicit root indices
    Vector{Any},                                        # [(:C,m),(:C,n-m)] | [(:C,m),nm] | [:A,n-1] | [:D,n]
    Tuple{Symbol,Int},                                  # (:A,n-1) or (:D,n)
    Tuple{Tuple{Symbol,Int},Int},                       # (:A,m)×n_m | (:D,m)×n_m
    Tuple{Tuple{Symbol,Int},Tuple{Symbol,Int}},         # (:A,m)×(:A,n-m-1) | (:D,m)×(:D,n-m)
    Tuple{Int,Int},                                     # (k, nk) type B/C
    Vector{Tuple{Symbol,Int}}                           # [(:C,m),(:C,n-m)] (also covered by Vector{Any})
}

# w: anisotropic (black) nodes OR their descriptors
const WInput = Union{
    Vector{QQMatrix},
    Vector{Int},
    Tuple{Int,Int},                                   # (d, r)
    Tuple{Tuple{Int,Int},Tuple{Int,Int}},              # ((d1,r1),(d2,r2))
    Vector{Tuple{Int,Int}},                            # [(d1,r1),(d2,r2)]
    Tuple{Int,Int,Int},                                # (x, r, d) type D
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
        throw(ArgumentError("_validate_v: unsupported root system type $S"))

    if v isa Vector{QQMatrix}
        for r in v
            r in [root(R, i).vec for i=1:num_roots(R)] || throw(ArgumentError("_validate_v: root not in R"))
        end
        return
    elseif v isa Vector{<:RootSystem}
        for r in v
            r in roots(R) || throw(ArgumentError("_validate_v: root not in R"))
        end
        return
    elseif v isa RootSystem
        return v in roots(R) ? nothing : throw(ArgumentError("_validate_v: root not in R"))
    end

    # ---- type A -------------------------------------------------------------
    if S == :A
        if v isa Tuple || v isa Vector
            # descriptor form: [(:X,m), n_m] or [(:X,m),(:A,n-m-1)]
            typeof(v[1]) <: Tuple || throw(ArgumentError("_validate_v: type-A descriptor must start with (:A, m)"))
            v[1][1] == :A || throw(ArgumentError("_validate_v: type-A subsystem must be of the form (:A, m)"))
            m = v[1][2]
            2 <= m <= n_rank || throw(ArgumentError("_validate_v: type-A m=$m out of range 2:$n_rank"))
            if typeof(v[2]) <: Tuple       # (:A,m) × (:A,n-m-1)
                v[2][1] == :A || throw(ArgumentError("_validate_v: second descriptor must be (:A, n-m-1)"))
                m2 = v[2][2]
                m + m2 + 1 == n_rank || throw(ArgumentError("_validate_v: (m,m2) do not partition A_$n_rank"))
            elseif v[2] isa Int           # (:A,m)^{n_m}
                (m + 1) * v[2] == n_rank + 1 ||
                    throw(ArgumentError("_validate_v: (:A,$m) repeated $(v[2])× does not fill A_$n_rank"))
            else
                throw(ArgumentError("_validate_v: type-A descriptor second element must be Int or (:A, ·)"))
            end
            return
        end
        throw(ArgumentError("_validate_v: type-A v must be a root, a Vector{Root}, or a descriptor tuple"))
        # ---- type B -----------------------------------------------------
    elseif S == :B
        if (v[1] isa Int) & (v[2] isa Int)
            k, nk = v
            1 <= k <= n_rank || throw(ArgumentError("_validate_v: type-$(S) k=$k out of range"))
            nk >= 1 || throw(ArgumentError("_validate_v: type-$(S) nk=$nk must be ≥ 1"))
            return
        elseif (v[1] isa Tuple) & (v[2] isa Tuple) #[(:B, m), (:B, n-m)]
            m = v[1][2]
            k = v[2][2]
            1 <= m <= n_rank-1 || throw(ArgumentError("_validate_v: type-$(S) k=$k out of range"))
            m + k == n_rank || throw(ArgumentError("_validate_v: type-$(S) subsystems not of correct rank."))
            return
        elseif (v[1] isa Tuple) & (v[2] isa Int)
            m = v[1][2]
            nm = v[2]
            m*nm==n_rank || throw(ArgumentError("_validate_v: type-$(S) m=$m, n_m=$nm out of range"))
            nm >= 2 || throw(ArgumentError("_validate_v: type-$(S) nk=$nk must be ≥ 2"))
            return
        end
        throw(ArgumentError("_validate_v: type-$(S) v must be (k, nk), an index vector, or [(:B, m), (:B, n-m)]"))

        # ---- type C -----------------------------------------------------
    elseif S == :C
        if v isa Tuple
            # (k, nk) — cyclic lift
            if v[1] isa Int && v[2] isa Int
                k, nk = v
                1 <= k <= n_rank || throw(ArgumentError("_validate_v: type-$(S) k=$k out of range 1:$n_rank"))
                nk >= 1 || throw(ArgumentError("_validate_v: type-$(S) nk=$nk must be ≥ 1"))
                return
            end
            # (:A, n-1) or (:D, n) — whole-subsystem descriptor
            if v[1] isa Symbol && length(v) == 2 && v[2] isa Int
                v[1] == :A && v[2] == n_rank - 1 && return
                v[1] == :D && v[2] == n_rank && return
            end
            throw(ArgumentError("_validate_v: type-$(S) v must be (k, nk), (:A, n-1), or (:D, n)"))
        elseif v isa Vector
            if isempty(v)
                return
            end
            # explicit integer root indices
            if all(x -> x isa Int && 1 <= x <= n_roots, v)
                return
            end
            # descriptor vector: [(:C,m),(:C,m2)] | [(:C,m),nm] | [:A,n-1] | [:D,n]
            if length(v) == 2
                if v[1] isa Tuple && v[1][1] == :C
                    m = v[1][2]
                    1 <= m <= n_rank - 1 || throw(ArgumentError("_validate_v: type-$(S) m=$m out of range 1:$(n_rank-1)"))
                    if v[2] isa Tuple          # [(:C,m),(:C,n-m)]
                        v[2][1] == :C || throw(ArgumentError("_validate_v: type-C second descriptor must be (:C, ·)"))
                        m2 = v[2][2]
                        m + m2 == n_rank || throw(ArgumentError("_validate_v: m+m2=$(m+m2) must equal n_rank=$n_rank"))
                        return
                    elseif v[2] isa Int        # [(:C,m),nm]  →  (C_m)^{nm}
                        m * v[2] == n_rank || throw(ArgumentError("_validate_v: (:C,$m) repeated $(v[2])× must fill C_$n_rank"))
                        return
                    end
                    throw(ArgumentError("_validate_v: type-C second descriptor must be (:C, ·) or Int"))
                elseif v[1] == :A && v[2] == n_rank - 1
                    return                        # [:A, n-1]
                elseif v[1] == :D && v[2] == n_rank
                    return                        # [:D, n]
                end
            end
            throw(ArgumentError("_validate_v: type-$(S) v must be an integer index vector, or a descriptor [(:C,m), …]/[:A,n-1]/[:D,n]"))
        end
        throw(ArgumentError("_validate_v: type-$(S) v must be (k, nk), an integer index vector, a descriptor, or a root"))

        # ---- type D -------------------------------------------------------------
    elseif S == :D
        if v isa Tuple
            typeof(v[1]) <: Tuple || throw(ArgumentError("_validate_v: type-D descriptor must start with a (…, m)"))
            if v[1][1] == :A
                m = v[1][2]
                m == n_rank - 1 || throw(ArgumentError("_validate_v: type-D (:A, m) needs m = n_rank-1"))
            elseif v[1][1] == :D
                m = v[1][2]
                3 <= m <= n_rank || throw(ArgumentError("_validate_v: type-D m=$m out of range 3:$n_rank"))
                if typeof(v[2]) <: Tuple
                    v[2][1] == :D || throw(ArgumentError("_validate_v: type-D second descriptor must be (:D, ·)"))
                    m2 = v[2][2]
                    m + m2 == n_rank || throw(ArgumentError("_validate_v: m+m2=$(m+m2) must equal n_rank=$n_rank"))
                elseif v[2] isa Int
                    (m + 1) * v[2] == n_rank || throw(ArgumentError("_validate_v: (:D,$m) repeated $(v[2])× must fill D_$n_rank"))
                else
                    throw(ArgumentError("_validate_v: type-D second descriptor must be Int or (:D, ·)"))
                end
            else
                throw(ArgumentError("_validate_v: type-D first descriptor must be :A or :D"))
            end
            return
        elseif v isa Vector
            if all(x -> x isa Int && 1 <= x <= num_roots(R), v)
                return                      # explicit root indices
            end
            if length(v) == 2 && v[1] isa Tuple && v[1][1] == :D
                m = v[1][2]
                3 <= m <= n_rank || throw(ArgumentError("_validate_v: type-D m=$m out of range 3:$n_rank"))
                if v[2] isa Tuple
                    v[2][1] == :D || throw(ArgumentError("_validate_v: type-D second descriptor must be (:D, ·)"))
                    m2 = v[2][2]
                    m + m2 == n_rank || throw(ArgumentError("_validate_v: m+m2=$(m+m2) must equal n_rank=$n_rank"))
                    return
                elseif v[2] isa Int
                    (m + 1) * v[2] == n_rank || throw(ArgumentError("_validate_v: (:D,$m) repeated $(v[2])× must fill D_$n_rank"))
                    return
                end
            end
        end
        throw(ArgumentError("_validate_v: type-D v must be a descriptor tuple, explicit roots, or empty vector"))
        # ---- type E (only E6 supported) ----------------------------------------
    elseif S == :E
        if l == 6
            if v isa RootSystem
                return v in roots(R) ? nothing : throw(ArgumentError("_validate_v: root not in R"))
            elseif v isa Vector{<:RootSystem}
                for r in v
                    r in roots(R) || throw(ArgumentError("_validate_v: root not in R"))
                end
                return
            elseif v isa Vector{QQMatrix}
                for r in v
                    r in [root(R, i).vec for i=1:num_roots(R)] || throw(ArgumentError("_validate_v: root not in R"))
                end
                return
            end
            throw(ArgumentError("_validate_v: type-E v must be a root or Vector{Root}"))
        end
        throw(ArgumentError("_validate_v: only E6 embedding is implemented"))
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
  - `(i,)` — the anisotropic pattern for type `B` (subsystem B_m^(n_m))

All `d` and `r` values must be `≥ 1`, and `x` must be `1` or `2`.
Explicit roots must belong to `R`. Throws `ArgumentError` otherwise.
"""
function _validate_w(R::RootSystem, w)
    if isempty(w)
        return
    end
    if w isa RootSystem
        return w in roots(R) ? nothing : throw(ArgumentError("p_a: anisotropic root not in R"))
    elseif w isa Vector{<:RootSystem}
        for r in w
            r in roots(R) || throw(ArgumentError("p_a: anisotropic root not in R"))
        end
        return
    elseif w isa Vector{QQMatrix}
        for r in w
            r in [root(R, i).vec for i=1:num_roots(R)] || throw(ArgumentError("p_a: root not in R"))
        end
        return
    end

    # descriptor tuples: shapes depend on the root-system class
    if w isa Tuple
        # (i,) — type B anisotropic pattern
        if w isa Tuple{Int}
            S, _ = root_system_type(R)[1]
            S == :B || throw(ArgumentError("_validate_w: w is only allowed to have one entry for type B."))
            (0 <= w[1]) || throw(ArgumentError("_validate_w: ((i,) entries must be ≥ 0"))
            return
        elseif w isa Tuple{Int,Int}                       # (d, r) — A/B/C, (:A,n-1) box
            (w[1] >= 1 && w[2] >= 1) ||
                throw(ArgumentError("p_a: (d, r) descriptors must be ≥ 1"))
            return
        elseif w isa Tuple{Tuple{Int,Int},Tuple{Int,Int}} # ((d1,r1),(d2,r2)) — A folded / D×D
            for (d, r) in w
                (d >= 1 && r >= 1) || throw(ArgumentError("p_a: ((d,r),(d,r)) entries must be ≥ 1"))
            end
            return
        elseif w isa Tuple{Int,Int,Int}                   # (x, r, d) — type D
            return (w[1] in (1, 2) && w[2] >= 1 && w[3] >= 1) ||
                throw(ArgumentError("p_a: (x, r, d) for D needs x ∈ {1,2}, r,d ≥ 1"))
        end
    end

    # [(d1,r1),(d2,r2)] — vector-of-tuple form (two-block, e.g. C_m × C_{n-m})  (new)
    if w isa Vector{<:Tuple{Int,Int}}
        for t in w
            (t[1] >= 1 && t[2] >= 1) || throw(ArgumentError("p_a: ((d,r),(d,r)) entries must be ≥ 1"))
        end
        return
    end

    throw(ArgumentError("p_a: w must be a root, explicit roots, or a descriptor tuple (d,r) / ((d,r),(d,r)) / (x,r,d)"))
end