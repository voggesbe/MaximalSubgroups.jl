using Oscar

"""
    to_elem(V, x)

Convert `x` (a `QQMatrix` row/column, or already a `Vector`) into a genuine
element of the free module / vector space `V`.
"""
to_elem(V, x) = V(vec(collect(x)))

"""
    col_span_matrix(V, vectors)

Build a matrix whose columns are the elements of `vectors` (each converted
via `to_elem`), i.e. a matrix spanning the same subspace of `V` that
`vectors` spans. Returns a 0-column matrix if `vectors` is empty.
"""
function col_span_matrix(V, vectors)
    isempty(vectors) && return zero_matrix(QQ, dim(V), 0)
    return transpose(matrix([to_elem(V, v) for v in vectors]))
end


"""
    extend_basis(V::Generic.FreeModule{QQFieldElem}, phi::Vector{<:QQMatrix}) -> Vector{QQMatrix}

Given a vector space `V` and a list of elements in V, `phi`, start with the first entry of phi
and extend this set recursively with every linearly independet element remaining in phi
"""
function extend_basis(V::Generic.FreeModule{QQFieldElem}, phi::Vector{Any})
    isempty(phi) && return QQMatrix[]
    chosen = [phi[1]]
    M = col_span_matrix(V, [phi[1]])

    for p in phi[2:end]
        cp = col_span_matrix(V, [p])
        if rank(hcat(M, cp)) > rank(M)
            push!(chosen, p)
            M = hcat(M, cp)
        end
    end
    return chosen
end
