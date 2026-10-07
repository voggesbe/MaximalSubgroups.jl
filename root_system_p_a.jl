using Revise, Oscar
using Graphs

include("validate_inpute_types.jl")
include("descriptor_resolver.jl")
include("permutation_matrix.jl")
include("root_system_helpers.jl")
# ---- Embedding helpers --------------------------------------------------


@doc raw"""
    p_a(R::RootSystem, v::VInput, w::WInput, f::PermGroupElem)

Return the anisotropic system phi_a for the root system phi with quasimaximal subsystem
  specified by the roots in v and anisotropic roots specified in w and f where f
  is a permutation specifying an index mapping from R to R
  if the index of the quasimaximal subsystem is of the form X^(d,r)_n, where X=A,D
    we can also type v = [(:X,n)], w = (d,r)
"""
function p_a(R::RootSystem, v, w, f::PermGroupElem)
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
    w2 = reduce(vcat, w2)
    #compute the orthogonal complement of E_{Delta_0}
    if length(w2) == 0
        U0 = identity_matrix(QQ, dim(V2))
    else
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
    s_R = extend_basis(V0, phi)

    # find the irreducible components in the root system
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
    #return phi, C, root_system_G
    return root_system_G, I, B, s_R, F
end
#Example1:
# R = root_system(:A, 8)
# v = [R[1], R[2], R[4], R[5], R[7], R[8]]
# w = []
# f = cperm([1,4],[2,5])

#Example2:
# R = root_system(:D, 4)
# v = [R[1], R[3], R[4], R[12]]
# w = [R[1], R[3]]
# f = cperm([1,12],[2,22],[3,4])

#Example2:
# R = root_system(:E, 6)
# v = [R[2], R[3], R[4], R[5]]
# w = [ ]
# f = cperm([2,3,5],[6,1,36])

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

#get the permutation of roots for the inner automorphisms for type A and D
function subindex(R::RootSystem, v, e::Int)
    S, n = root_system_type(R)[1]
    ro = [root(R, i).vec for i = 1:num_roots(R)]
    if S == :A #for type A
        if typeof(v[2]) <: Int #subsystem type A_i^(m_i) in A_n
            if (v[1][2]+1)*v[2] == n+1
                if e == 1 #not folded
                    f = cperm([[(j-1)*(v[1][2]+1)+k for j = 1:v[2]] for k = 1:v[1][2]])
                elseif e == 2 #folded
                    v0 = [[(j-1)*(v[1][2]+1)+k for j = 1:v[2]] for k = 1:v[1][2]]
                    v1 = [[v0[k], reverse(v0[length(v0)-k+1])] for k=1:Int(floor(v[1][2]/2))]
                    v2 = [reduce(vcat, v1[i]) for i = 1:length(v1)]
                    if v[1][2] % 2 == 1
                        v3 = [Int((v[1][2]+1)/2)+i*(v[1][2]+1) for i = 0:(v[2]-1)]
                        v2 = vcat(v2, [v3])
                    end
                    f = cperm(v2)
                end
            end
        elseif typeof(v[2]) <: Tuple #subsystem type [(:A_m),(:A,n-m-1)]
            m = v[1][2]
            k = v[2][2]
            v1 = [[i, m-i+1] for i = 1:Int(floor(m/2))]
            v2 = [[m+1+i, n-i+1] for i = 1:Int(floor(k/2))]
            f = cperm(vcat(v1, v2))
        end
    elseif S == :D #for type D
        #embedding into the vector space
        _, _, E, m, m0 = simple_root_embedding(R)
        if v[1][1] == :A #subsystem (:A,n-1)
            j = findall(==(-ro[n]), ro)[1]
            if n % 2 == 0 #subsytem A_(n-1) has odd number of roots
                f1 = [[i, n-i] for i=1:Int(floor((n-1)/2))]
                f = cperm(f1)
            elseif n % 2 == 1 #even number of roots 
                if e == 1
                    #f = cperm()
                    f = cperm([n-1, n])
                elseif e == 2
                    f1 = [[i, n-i] for i=1:Int(floor((n-1)/2))]
                    f2 = vcat(f1, [[n, j]])
                    f = cperm(f2)
                end
            end
        elseif length(v) == 2 && typeof(v[2]) <: Tuple #subsystem type [(:D_m), (:D,n-m)]
            n1 = Int(length(ro)/2)
            j1 = findall(==(-ro[n1]), ro)[1]
            f = cperm([j1, 1], [n, n-1])
        elseif length(v) == 2 && typeof(v[2]) <: Int #subsytem type [(:D,m),n_m]
            f1 = [[k+v[1][2]*i for i = 0:(v[2]-1)] for k = 1:(v[1][2]-1)]
            if e % 2 == 1 #no fold at the end of each D_m
                f2 = [findall(==((E[i*v[1][2]-1, :]+E[i*v[1][2], :])*inv(m0)), ro)[1] for i = 1:v[2]]
                f = cperm(vcat(f1, [f2]))
            elseif e % 2 == 0 #folded
                f2 = [findall(==((E[i*v[1][2]-1, :]+E[i*v[1][2], :])*inv(m0)), ro)[1] for i = 1:v[2]]
                #f3 = [[findall(==((E[i*v[1][2]-1,:]+E[i*v[1][2],:])*inv(m0)),ro)[1],i*v[1][2]-1] for i = 1:v[2]]
                f1[end] = vcat(f1[end], f2)
                #f = cperm(vcat(f1,[f2],f3))
                f = cperm(f1)
            end
        end
    end
    return f
end

function simple_root_vector(R::RootSystem)
    return [root(R, i) for i = 1:rank(R)]
end

#Example: C_12
# R = root_system(:C, 12)
# # v=(k,nk)
# v = (4, 3)
# # w=(d,r) where r is the number of white dots and d is the dots between them
# w = (2, 2)
# f = cperm()
# Phi_a, E_s, E_a, s_R = p_a(R, v, w, cperm());
# # should return [(:A, 5), 2]

#Example: A_23
# R = root_system(:A, 23)
# v = [(:A, 7), 3]
# w = (2, 1)
# f = subindex(R, v, 2)
# Phi_a, E_s, E_a, s_R = p_a(R, v, w, f)
#should return [[(:A,5), 2], [(:A,11), 1]]

#Example: D_30
R = root_system(:D, 30);
v = [(:D, 20), (:D, 10)]
w = ((4, 3), (4, 1))
f = subindex(R, v, 2)
Phi_a, E_s, E_a, s_R, F = p_a(R, v, w, f);

# v= [(:D,10),3]
# w = (2,3)
# f = subindex(R, v, 2)
#Phi_a, E_s, E_a, s_R, F = p_a(R,v,w,f);
