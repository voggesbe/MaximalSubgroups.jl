using Oscar
using Graphs

# ---- Embedding helpers --------------------------------------------------


@doc raw"""
    anisotropic_system(R::RootSystem, v::VInput, w::WInput, f::PermGroupElem)

Return the anisotropic system phi_a for the root system phi with quasimaximal subsystem
  specified by the roots in v and anisotropic roots specified in w and f where f
  is a permutation specifying an index mapping from R to R
  if the index of the quasimaximal subsystem is of the form X^(d,r)_n, where X=A,D
    we can also type v = [(:X,n)], w = (d,r)
"""
function anisotropic_system(R::RootSystem, v, w, f::PermGroupElem)
    n_rank = num_simple_roots(R)
    # compute the roots in the subroot system
    ro = [root(R, i).vec for i = 1:num_roots(R)]
    #emebed root system into vector space
    V1, V2, E, m, m0 = simple_root_embedding(R)

    # check that v and w are of the correct/ allowed forms
    _validate_v(R, v)
    _validate_w(R, w)
    # assemble lists v= roots of subsystem and w = list of black nodes in subsystem if not already given

    v, w, f=_resolve_vw(R, v, w, f, E, m0)

    V0 = VectorSpace(QQ, n_rank)

    #compute the matrix for the map specified by f w.r.t the basis spanned by the simple roots
    F = permutation_to_matrix(f, ro, m0)
    #compute the fixed point space under F, that is we want the eigenvectors with eigenvalue
    # 1 for F
    eig = eigenspaces(F)
    if haskey(eig, QQ(1))
        Es = eig[QQ(1)]
    else
        Es = []
    end

    # if there exists a non-empty perp-space of span(v), we want nothing to be fixed in it
    # so compute this perp space and only take the fixed points in the remaining space, i.e.
    # intersect the fixed space Es with span(v)

    v2 = [v[i]*m0 for i = 1:length(v)]
    #compute the intersection of the fixed point space given by Es and v2

    M = append!([to_elem(V2, Es[i, :]) for i = 1:nrows(Es)], [to_elem(V2, v2[i]) for i = 1:length(v2)])
    M = matrix(M)
    if length(Es) == 0
        K = [] #intersection is empty
    else
        K = kernel(M)
        K2 = K[:, 1:nrows(Es)]
        Es2 = K2*Es #basis of intersection are column vectors of Es2
    end

    w2 = [w[i]*m0 for i = 1:length(w)] #vectors corresponding to the anisotropic roots in w
    #compute the orthogonal complement of E_{Delta_0}
    if length(w2) == 0
        U0 = identity_matrix(QQ, dim(V2))
    else
        w2 = reduce(vcat, w2)
        U0 = orthogonal_complement(V1, matrix(w2))
    end

    #compute the intersection of the fixed point space given by Es2 and U0
    M = append!([to_elem(V2, Es2[i, :]) for i = 1:nrows(Es2)], [to_elem(V2, -U0[i, :]) for i = 1:nrows(U0)])
    M = matrix(reduce(vcat, M))
    if length(Es2) == 0
        I = 0*M #intersection is empty
        phi = ro
    else
        K = kernel(M)
        K2 = K[:, 1:nrows(Es2)]
        I = K2*Es2 #basis of intersection are column vectors of I
        #compute orthogonal complement orth_I of I
        orth_I = orthogonal_complement(V1, I)
        #compute the intersection of orth_I with the root system
        B = transpose(orth_I)
        M = hcat(B, (-1)*m[:, 1:(end-1)])
        K3 = kernel(transpose(M))
        K4 = K3[:, 1:nrows(B)]
        I2 = K4*B
        phi = []
        for i = 1:num_roots(R)
            b = matrix(ro[i]*m0)
            if can_solve(B, transpose(b), side=:right)
                append!(phi, [ro[i]])
            end
        end
    end


    if phi == []
        return phi, I, B, [], F
    end
    #check what kind of root system we have
    # find the simple roots
    root_system_G, s_R = find_root_system_type(phi, m0, V2, V0)

    #return phi, C, root_system_G
    return root_system_G, I, B, s_R, F
end


