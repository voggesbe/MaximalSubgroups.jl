using Revise, Oscar
using Graphs
@doc raw"""
    p_a(R::RootSystem, v::Vector{RootSystem}, w::Vector{RootSystem}, f::PermGroupElem)

Return the anisotropic system phi_a for the root system phi with quasimaximal subsystem
  specified by the roots in v and anisotropic roots specified in w and f where f
  is a permutation specifying and index mapping from R to R
"""
function p_a(R::RootSystem, v, w, f)
  n = num_simple_roots(R)
  # compute the roots in the subroot system
  S,l = root_system_type(R)[1]
  ro = [root(R, i).vec for i = 1:num_roots(R)]
  s_ro = [simple_root_vector(R)[i].vec for i = 1:rank(R)]
  #compute the orthogonal space
  if S == :A
    #we embed into R^(n+1) with R[i]= e_i-e_i+1
    V2 = VectorSpace(QQ, n + 1)
    V1 = quadratic_space(QQ, n + 1)
    E = identity_matrix(QQ, n + 1)
    m0 = [V2(transpose(E[:, i] - E[:, i+1])) for i = 1:n]
    m0 = matrix(m0)
    m1 = append!([V2(transpose(E[:, i] - E[:, i+1])) for i = 1:n], [V2(transpose(E[:, n+1]))])
    m = transpose(matrix(m1)) #vectors for simple roots
  elseif S == :B
    V2 = VectorSpace(QQ, n)
    V1 = quadratic_space(QQ, n)
    E = identity_matrix(QQ, n)
    m0 = append!([V2(transpose(E[:, i] - E[:, i+1])) for i = 1:n-1], [V2(transpose(E[:, n]))])
    m0 = matrix(m0)
    m = transpose(m0) #vectors for simple roots
  elseif S == :C
    V2 = VectorSpace(QQ, n)
    V1 = quadratic_space(QQ, n)
    E = identity_matrix(QQ, n)
    m0 = append!([V2(transpose(E[:, i] - E[:, i+1])) for i = 1:n-1], [V2(transpose(2*E[:, n]))])
    m0 = matrix(m0)
    m = transpose(m0) #vectors for simple roots
  elseif S == :D
    V2 = VectorSpace(QQ, n)
    V1 = quadratic_space(QQ, n)
    E = identity_matrix(QQ, n)
    m0 = [V2(transpose(E[:, i] - E[:, i+1])) for i = 1:n-1]
    append!(m0, [V2(transpose(E[:, n-1] + E[:, n]))])
    m0 = matrix(m0)
    m = transpose(m0) #vectors for simple roots
  elseif S == :E
    if l == 6
      V2 = VectorSpace(QQ, 9)
      V1 = quadratic_space(QQ, 9)
      E = identity_matrix(QQ, 9)
      m0 = [V2(transpose(E[:, i] - E[:, i+1])) for i = 2:8]
      m0 = [m0[7], m0[1], m0[6], V2([1 // 3, -2 // 3, 1 // 3, -2 // 3, 1 // 3, 1 // 3, -2 // 3, 1 // 3, 1 // 3]), m0[3], m0[4]]
      m0 = matrix(m0)
      m = hcat(transpose(m0), E[:,1], E[:,4], E[:,7]) #vectors for simple roots
    end
  end
# assemble lists v= roots of subsystem and w = list of black nodes in subsystem
    # TODO: even this out, so that we can give w = (r,d) as in Tits' paper for each root system
  v2 = []
  if S == :A
    if typeof(v[1]) <: Tuple
      if typeof(v[2]) <: Tuple
        v2 = vcat(ro[1:v[1][2]], ro[v[1][2]+2:v[1][2]+v[2][2]+1])
        s = (v[1][2], v[2][2])
      elseif typeof(v[2]) <: Int
        for i = 1:v[2]
          append!(v2, ro[(i-1)*(v[1][2]+1)+1:i*(v[1][2]+1)-1])
          s = (v[1][2], v[2])
        end
      end
      v = v2
    end
    #anisotropic nodes. In A_n there are the possible subsystems of type A_i^(m_i) and A_mA_(n-m)
    if typeof(w) <: Tuple
      if length(w) == 1
        k = w[1]
        w2 = deleteat!(copy(s_ro), [i * k for i = 1:Int((n + 1) / k)-1])
        w = w2
      elseif length(w) == 2
        k1 = w[1]
        k2 = w[2]
        if typeof(k1) <: Tuple && length(k1) == 2
          d1 = k1[1]
          r1 = k1[2]
          x1_1 = vcat([i * d1 for i = 1:r1], [(i * d1 + s[1] - 2 * r1 * d1 + 1) for i = r1:2*r1-1])
          x1_2 = Set{Int}(x1_1)
          x1 = [x for x in x1_2]
          w_1 = deleteat!(copy(v2[1:s[1]]), sort(x1))
        elseif length(k1) == 1 || typeof(k1) <: Int
          k1 = k1[1]
          w_1 = deleteat!(copy(v2[1:s[1]]), [i * k1 for i = 1:Int((s[1] + 1) / k1)-1])
        end
        if typeof(k2) <: Tuple && length(k2) == 2
          d2 = k2[1]
          r2 = k2[2]
          v3 = copy(v2[s[1]+1:end])
          x2_1 = vcat([i * d2 for i = 1:r2], [(i * d2 + s[2] - 2 * r2 * d2 + 1) for i = r2:2*r2-1])
          x2_2 = Set{Int}(x2_1)
          x2 = [x for x in x2_2]
          w_2 = deleteat!(copy(v3), sort(x2))
        elseif length(k2) == 1 || typeof(k2) <: Int
          w_2 = deleteat!(copy(v2[s[1]+1:end]), [i * w[2] for i = 1:Int((s[2] + 1) / k2)-1])
        end
        w = vcat(w_1, w_2)
      elseif length(w) == 3
        d = w[1]
        r = w[2]
        v1 = [v2[i:i+s[1]-1] for i in [k*s[1]+1 for k = 0: s[2]-1]]
        w0 = []
        for j = 1: length(v1)
          y = copy(v1[j])
          x_1 = vcat([i * d for i = 1:r], [(i * d + s[1] - 2 * r * d + 1) for i = r:2*r-1])
          x_2 = Set{Int}(x_1)
          x = [z for z in x_2]
          w_1 = deleteat!(copy(y), sort(x))
          append!(w0,w_1)
        end
        w = w0
      end
    end
  elseif S == :B
    if typeof(v) <: Tuple
      k = v[1]
      nk = v[2]
      num_list = []
      for m = 0:nk-2
        num_list = vcat(num_list, [m * k + i for i = 1:k-1])
      end
      for m = 0:nk-2
        num_list = vcat(num_list, findall(==(-1 * (sum([ro[i] for i = m*k+1:n]))), ro)[1])
      end
      v0 = vcat(num_list, [i for i in (nk-1)*k+1:n])
      v = [ro[v0[i]] for i = 1:length(v0)]
    end
    if typeof(w) <: Tuple
      num_tup = []
      for m = 0:nk-2
        num_tup = vcat(num_tup, findall(==(-1 * (sum([ro[i] for i = m*k+1:n]))), ro)[1])
      end
      num_tup = vcat(num_tup, n)
      num_tup_2 = []
      for r = 1:k-1
        num_tup_2 = vcat(num_tup_2, [[]])
        num_tup_2[r] = [m * k + r for m = 0:nk-2]
        num_tup_2[r] = vcat(num_tup_2[r], n - r)
      end
      c = vcat(Vector{Int64}[num_tup], num_tup_2)
      f = cperm([reduce(vcat, c[i]) for i = 1:length(c)])
      i = w[1]
      w = []
      for j = 1:i
        w = vcat(w, ro[c[j]])
      end
    end
  elseif S == :C
    if typeof(v) <: Tuple
      if length(v) == 2
          k = v[1]
          nk = v[2]
          num_list = []
          for m = 0:nk-2
            num_list = vcat(num_list, [m*k + r for r = 1:k-1])
          end
          for m = 0:nk-2
            num_list = vcat(num_list, findall(==(-1*(2*sum([ro[i] for i = m*k+1:n-1])+ro[n])), ro)[1])
          end
          v0 = vcat(num_list, [n-r for r in 0:k-1])
          v = [ro[v0[i]] for i = 1:length(v0)]
          if typeof(w) <: Tuple
            d=w[1]
            r=w[2]
            num_tup = [];
            for m = 0:nk-2
              num_tup = vcat(num_tup, findall(==(-1*(2*sum([ro[i] for i = m*k+1:n-1])+ro[n])), ro)[1]);
            end
            num_tup = vcat(num_tup,n);
            num_tup_2 = [];
            for r = 1:k-1
              num_tup_2 = vcat(num_tup_2, [[]])
              num_tup_2[r] = [m * k + r for m = 0:nk-2]
              num_tup_2[r] = vcat(num_tup_2[r], n - r)
            end
            c = vcat(Vector{Int64}[num_tup], num_tup_2)
            f = cperm([reduce(vcat, c[i]) for i = 1:length(c)])
            if k == r*d
              w = [];
              for j = 0:r-1
                for i in 2:d
                  w = vcat(w, ro[c[j*d+i]])
                end
              end
            else
              w = [];
              for i in 1:k-r*d
              w = vcat(w, ro[c[i]])
              end
              for m = 1:r
                for i in 2:d
                  w = vcat(w, ro[c[k-m*d+i]])
                end
              end
            end              
          end
      elseif length(v) == 0
        v0 = [r for r = 1:n-1]
        v = [ro[v0[i]] for i = 1:length(v0)]
        d=w[1]
        r=w[2]
        num_tup_2=[];
        if iseven(n) == true
          for r = 1:Int(n/2-1)
            num_tup_2 = vcat(num_tup_2, [[]])
            num_tup_2[r] = [r,n-r]
          end
        else
          for r = 1:Int((n-1)/2)
            num_tup_2 = vcat(num_tup_2, [[]])
            num_tup_2[r] = [r,n-r]
          end
        end
        c = vcat(num_tup_2)
        f = cperm([reduce(vcat, c[i]) for i = 1:length(c)])
        x_1 = vcat([i * d for i = 1:r], [n-i*d for i = 1:r])
        x_2 = Set{Int}(x_1)
        x = [z for z in x_2]
        w2 = deleteat!(copy(v), sort(x))
        w = w2
      end
    end
  elseif S == :D
        # here, we give w=(x,r,d), where (r,d) are as in Tits' paper and x is either 1
        # or 2, depending on whether we have an automorphism act on A_(n-1) or not
    if v[1][1] == :A
      v2 = ro[1:v[1][2]]
      s = v[1]
      v = v2
      r = w[2]
      d = w[3]
      if w[1] == 1
        w2 = deleteat!(copy(v2), [i * d for i = 1:Int((n) / d)-1])
      elseif w[1] == 2
        x_1 = vcat([i * d for i = 1:r], [n-i*d for i = 1:r])
        x_2 = Set{Int}(x_1)
        x = [z for z in x_2]
        w2 = deleteat!(copy(v2), sort(x))
      end
      w = w2
      v = v2
    elseif v[1][1] == :D && typeof(v[2]) <: Tuple
      z = transpose(-E[:, 1] - E[:, 2])*inv(m0)
      v2 = vcat(z,ro[1:v[1][2]-1],ro[v[1][2]+1:n])
      d1 = w[1][1]
      r1 = w[1][2]
      d2 = w[2][1]
      r2 = w[2][2]
      x1 = [v[1][2]-i*d1+1 for i = 1:r1]
      if d1*r1 +1 == v[1][2]
        x1 = vcat(x1,[1,2])
        x1 = Set{Int}(x1)
        x1 = [z for z in x1]
      end
      x2 = [v[1][2]+i*d2 for i = 1:r2]
      if d2*r2 +1 == n-v[1][2]
        x2 = vcat(x2,[n,n-1])
        x2 = Set{Int}(x2)
        x2 = [z for z in x2]
      end
      x = vcat(x1,x2)
      w2 = deleteat!(copy(v2), sort(x))
      w = w2
      v = v2
    elseif v[1][1] == :D && typeof(v[2]) <: Int
      v2 = []
      for i = 1:v[2]-1
        a = v[1][2]*(i-1)
        z = transpose(E[:, a+v[1][2]-1] + E[:, a+v[1][2]])*inv(m0)
        v2 = vcat(v2,ro[a+1:a+v[1][2]-1],z)
      end
      a = v[1][2] * (v[2] - 1)
      v2 = vcat(v2,ro[a+1:n])
    end
  end
  V0 = VectorSpace(QQ, n)

  #compute the matrix for the map specified by f w.r.t the basis spanned by the simple roots
  m2 = 1*E
  Sy = parent(f);
  l = Oscar.degree(Sy);
  Ba = 1*E
  k = 1
  for i = 1:l
    if k > dim(V2)
      break
    end
    j = f(i)
    if i != j && !(can_solve(Ba[:,1:(k-1)], transpose(ro[i]*m0)))
      Ba[:,k] = transpose(ro[i]*m0) #make a basis out of the not fixed roots
      r = vcat([ro[j][k] for k = 1:length(ro[j])], [0*i for i = n+1:dim(V2)])
      m2[:, k] = r
      k = k+1
    end
  end
  if k <= dim(V2)
    for i = 1:n
      if k > dim(V2)
        break
      end
      j = f(i)
      if i == j && !(can_solve(Ba[:,1:(k-1)], transpose(ro[i]*m0)))
        Ba[:,k] = transpose(ro[i]*m0) #make a basis out of the remaining simple roots
        r = vcat([ro[j][k] for k = 1:length(ro[j])], [0*i for i = n+1:dim(V2)])
        m2[:, k] = r
        k = k+1
      end
    end
  end

  #change of basis to standard basis
  F = m*m2*inv(Ba)
  #print(F)

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
  M = append!([V2(transpose(Es[:, i])) for i = 1:ncols(Es)], [V2(v2[i]) for i = 1:length(v2)])
  M = transpose(matrix(M))
  if length(Es) == 0
    K = [] #intersection is empty
  else
    K = kernel(M)
    K2 = K[2][1:ncols(Es), :]
    Es2 = Es*K2 #basis of intersection are column vectors of Es2
  end

  w2 = [V2(w[i]*m0) for i = 1:length(w)] #vectors corresponding to the anisotropic roots in w
  #compute the orthogonal complement of E_{Delta_0}
  if length(w2) == 0
    U0 = identity_matrix(QQ, dim(V2))
  else
    U0 = orthogonal_complement(V1, matrix(w2))
  end

  #compute the intersection of the fixed point space given by Es2 and U1
  M = append!([V2(transpose(Es2[:, i])) for i = 1:ncols(Es2)], [V2(-U0[i,:]) for i = 1:nrows(U0)])
  M = transpose(matrix(M))
  if length(Es2) == 0
    K = [] #intersection is empty
  else
    K = kernel(M)
    K2 = K[2][1:ncols(Es2), :]
    I = Es2*K2 #basis of intersection are column vectors of I
  end
  #compute orthogonal complement orth_I of I
  orth_I = orthogonal_complement(V1, transpose(I))
  #compute the intersection of orth_I with R
  B = transpose(orth_I)
  M = hcat(B,(-1)*m[:,1:(end-1)])
  K3 = kernel(M)
  K4 = K3[2][1:ncols(B), :]
    I2 = B*K4
  phi = []
  for i = 1:num_roots(R)
    b = matrix([V2(ro[i]*m0)])
    if can_solve(B, transpose(b))
      append!(phi, [ro[i]])
    end
  end
  if phi == []
    return phi, [], []
  end
  #check what kind of root system we have
  # find the simple roots
  s_R = [phi[1]]
  for i = 1:length(phi)
    A = transpose(matrix([V0(s_R[i]) for i=1:length(s_R)]))
    b = transpose(matrix([V0(phi[i])]))
    if !can_solve(A, b)
      append!(s_R, [phi[i]])
    end
  end
  #compute the Cartan matrix
  v_sR = [matrix([V2(s_R[i] * m0)]) for i = 1:length(s_R)]
  C = diagonal_matrix(QQ(2), length(s_R))
  for i = 1:length(s_R)
    for j = 1:length(s_R)
      if i != j
        C[i, j] = 2 * (v_sR[j]*transpose(v_sR[i]))[1] / (v_sR[i]*transpose(v_sR[i]))[1]
      end
    end
  end
  k = length(s_R)
  #adjacency matrix
  A = Array{Int}(undef, k, k)
  for i = 1:k
    for j = 1:k
      if i == j
        A[i, j] = 0
      else
        A[i, j] = (C[i, j] * C[j, i]).num
      end
    end
  end
  # find the irreducible components in the root system with the help of A
  g = SimpleGraph(A)
  comp = Graphs.connected_components(g)
  irred_comps = [[s_R[comp[j][i]] for i = 1:length(comp[j])] for j = 1:length(comp)]
  irred_cartans = []
  for i = 1:length(irred_comps)
    s_Ri = irred_comps[i]
    v_sR = [matrix([V2(s_Ri[j] * m0)]) for j = 1:length(s_Ri)]
    Ci = diagonal_matrix(QQ(2), length(s_Ri))
    for j = 1:length(s_Ri)
      for k = 1:length(s_Ri)
        if j != k
          Ci[j, k] = 2 * (v_sR[k]*transpose(v_sR[j]))[1] / (v_sR[j]*transpose(v_sR[j]))[1]
        end
      end
    end
    append!(irred_cartans, [Ci])
  end
  # we can check what root system it is by checking for each indecomposable factor
  # if the JNF is the same as another cartan matrix of a root system with the same
  # rank
  root_system_G = []
  for i = 1:length(irred_cartans)
    C1 = irred_cartans[i]
    m = rank(C1)
    JNF1 = jordan_normal_form(C1)[1]
    types = [:A, :B, :C, :D, :E, :F, :G]
    j = 1
    Ma = matrix_space(QQ, m, m)
    JNF2 = jordan_normal_form(Ma(cartan_matrix(:A, m)))[1]
    while JNF2 != JNF1
      j = j + 1
      if types[j] == :E && m in [6, 7, 8]
        JNF2 = jordan_normal_form(Ma(cartan_matrix(types[j], m)))[1]
      elseif types[j] == :F && m == 4
        JNF2 = jordan_normal_form(Ma(cartan_matrix(types[j], m)))[1]
      elseif types[j] == :G && m == 2
        JNF2 = jordan_normal_form(Ma(cartan_matrix(types[j], m)))[1]
      else
        JNF2 = jordan_normal_form(Ma(cartan_matrix(types[j], m)))[1]
      end
    end
    x = 0
    if types[j] in [:B, :C]
      for i = 1:nrows(C1)
        for j1 = 1:ncols(C1)
          l = [i, j1]
          if C1[i, j1] == -2
            x = 1
            break
          end
        end
        if x == 1
          break
        end
      end
      s_Ri = irred_comps[i]
      v_sR = [matrix([V2(s_Ri[j] * m0)]) for j = 1:length(s_Ri)]
      v_sR2 = deleteat!(copy(v_sR), sort(l))
      l1 = (v_sR[l[1]]*transpose(v_sR[l[1]]))[1]
      l2 = (v_sR[l[2]]*transpose(v_sR[l[2]]))[1]
      l3 = (v_sR2[1]*transpose(v_sR2[1]))[1]
      if l1 == l3
        if l2 < l1
          types[j] = :B
        else
          types[j] = :C
        end
      elseif l2 == l3
        if l1 < l2
          types[j] = :B
        else
          types[j] = :C
        end
      end
    end
    ro = [root_system_G[i][1] for i = 1:length(root_system_G)]
    if (types[j], m) in ro
      j = findfirst(==((types[j], m)), ro)
      root_system_G[j][2] += 1
    else
      append!(root_system_G, [[(types[j], m), 1]])
    end
  end
  #return phi, C, root_system_G
  return root_system_G, I, B, s_R
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
  S,n = root_system_type(R)[1]
  if S == :A
    s1 = []
    s2 = []
    div = divisors(n + 1)
    for i in div
      if (n+1)/i >= 3 && i-1 > 0
        append!(s1, [[(:A,i-1),Int((n+1)/i)]])
      end
    end
    s2 = [[(:A,j),(:A,n-1-j)] for j = 0:Int(floor((n-1)/2))]
  end
  return s1,s2
end

#get the permutation of roots for the inner automorphisms on the root systems of type A_i^(m_i) in A_n
function subindex(R, v, w, e)
  S,n = root_system_type(R)[1]
  ro = [root(R, i).vec for i = 1:num_roots(R)]
  if S == :A
    if typeof(v[2]) <: Int
      if (v[1][2]+1)*v[2] == n+1
        if e == 1
          f = cperm([[(j-1)*(v[1][2]+1)+k for j = 1:v[2]] for k = 1:v[1][2]])
       elseif e == 2
          v1 = [[[k + m * (v[1][2] + 1), (m + 1) * (v[1][2] + 1) - k] for m = 0:(v[2]-1)] for k = 1:Int(floor(v[1][2] / 2))]
          v2 = [ reduce(vcat, v1[i]) for i= 1: length(v1)]
          if v[1][2] % 2 == 1
            v3 = [Int((v[1][2]+1)/2)+i*(v[1][2]+1) for i = 0: (v[2]-1)]
            v2 = vcat(v2,[v3])
          end
          f = cperm(v2)
        end
      end
    elseif typeof(v[2]) <: Tuple
      m = v[1][2]
      k = v[2][2]
      v1 = [[i,m-i+1] for i = 1:Int(floor(m/2))]
      v2 = [[m+1+i,n-i+1] for i = 1:Int(floor(k/2))]
      f = cperm(vcat(v1,v2))
    end
  elseif S == :D
    if v[1][1] == :A
      j = findall(==(-ro[n]),ro)[1]
      if n % 2 == 0
        f1 = [[i,n-i] for i=1:Int(floor((n-1)/2))]
        f = cperm(f1)
      elseif n % 2 == 1
        if e == 1
          #f = cperm()
          f = cperm([n,j])
        elseif e == 2
          f1 = [[i,n-i] for i=1:Int(floor((n-1)/2))]
          f2 = vcat(f1,[[n,j]])
          f = cperm(f2)
        end
      end
    elseif length(v) == 2 && typeof(v[2]) <: Tuple
       n1 = Int(length(ro)/2)
       j1 = findall(==(-ro[n1]),ro)[1]
      f = cperm([j1,1],[n,n-1])
    end
  end
  return f
end

function simple_root_vector(R::RootSystem)
  return [root(R,i) for i = 1:rank(R)]
end

#Example: C_12
#R = root_system(:C, 12)
#v=(k,nk)
#v = (4,3)
#w=(d,r) where r is the number of white dots and d is the dots between them
#w = (2,2)
#Phi_a, E_s, E_a, s_R = p_a(R,v,w,cperm());

#Example: A_23
#R = root_system(:A, 23)
#v = [(:A, 7), 3]
#w = (2, 1, [2])
#f = subindex(R, v, w, 2)
