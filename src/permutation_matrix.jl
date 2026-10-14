using Oscar

@doc raw"""
    permutation_to_matrix(f::PermGroupElem, ro::Vector{QQMatrix}, m0::QQMatrix) -> QQMatrix

Return the matrix `F` (acting on column vectors of the ambient space V = ℚ^d)
of the linear map determined by the permutation `f` of the root indices.

- `ro[i]` is root `i` as a 1×n_rank row vector in simple-root coordinates.
- `m0` is the n_rank×d matrix whose rows are the simple roots in V, so that
  root `i` is the column `transpose(ro[i] * m0)` in V.

`F` is built from a basis of span(Φ) consisting of roots: first the roots moved
by `f`, then the simple roots fixed by `f`. Each basis root is sent to its image
under `f`. On the orthogonal complement of span(Φ) in V, `F` is the identity.
Hence `F * transpose(ro[i]*m0) == transpose(ro[f(i)]*m0)` for every basis root.
"""
function permutation_to_matrix(f::PermGroupElem, ro::Vector{QQMatrix}, m0::QQMatrix)
    n_rank = nrows(m0)
    deg = Oscar.degree(parent(f))
    fi(i) = i <= deg ? Int(f(i)) : i            # points outside the group's degree are fixed

    root_col(i) = transpose(ro[i] * m0)         # root i as a d×1 column in V

    src = QQMatrix[]                            # chosen roots (linearly independent columns)
    img = QQMatrix[]                            # their images under f

    function try_add!(i)
        c = root_col(i)
        # c is independent of the chosen roots iff appending it raises the rank
        if isempty(src) || rank(hcat(reduce(hcat, src), c)) > length(src)
            push!(src, c)
            push!(img, root_col(fi(i)))
        end
    end

    # 1. roots moved by f
    for i in 1:length(ro)
        length(src) == n_rank && break
        fi(i) != i && try_add!(i)
    end
    # 2. complete with simple roots fixed by f
    for i in 1:n_rank
        length(src) == n_rank && break
        fi(i) == i && try_add!(i)
    end
    length(src) == n_rank ||
        error("permutation_to_matrix: could not find $n_rank independent roots (found $(length(src)))")

    # 3. identity on the orthogonal complement of the root span
    S = reduce(hcat, src)
    T = reduce(hcat, img)
    Q = nullspace(m0)[2]                        # d×(d-n_rank), m0*Q = 0
    if ncols(Q) > 0
        S = hcat(S, Q)
        T = hcat(T, Q)
    end

    # F*S = T
    return T * inv(S)
end

@doc raw"""
    permutation_to_matrix_old(f::PermGroupElem, E::QQMatrix)

compute the matrix for the map specified by f w.r.t the basis spanned by the simple roots
"""
function permutation_to_matrix_old(f::PermGroupElem, E::QQMatrix, V, n_rank::Int, ro::Vector{QQMatrix}, m0, m)
    m2 = 1*E
    Sy = parent(f)
    l = Oscar.degree(Sy)
    Ba = 1*E
    k = 1
    for i = 1:l
        if k > dim(V)
            break
        end
        j = f(i)
        if i != j
            if isempty(Ba[:, 1:(k-1)]) || !(can_solve(Ba[:, 1:(k-1)], transpose(ro[i]*m0)))
                Ba[:, k] = transpose(ro[i]*m0) #make a basis out of the not fixed roots
                r = vcat([ro[j][k] for k = 1:length(ro[j])], [0*i for i = (n_rank+1):dim(V)])
                m2[:, k] = r
                k = k+1
            end
        end
    end
    if k <= dim(V)
        for i = 1:n_rank
            if k > dim(V)
                break
            end
            j = f(i)
            if i == j
                if isempty(Ba[:, 1:(k-1)]) || !(can_solve(Ba[:, 1:(k-1)], transpose(ro[i]*m0)))
                    Ba[:, k] = transpose(ro[i]*m0) #make a basis out of the remaining simple roots
                    r = vcat([ro[j][k] for k = 1:length(ro[j])], [0*i for i = (n_rank+1):dim(V)])
                    m2[:, k] = r
                    k = k+1
                end
            end
        end
    end

    #change of basis to standard basis
    F = m*m2*inv(Ba)
    return F
end