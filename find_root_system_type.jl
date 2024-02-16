using Revise, Oscar
using Graphs
function find_root_system_type(s_R, m0)
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
    if types[j] in [:B, :C] && m!=2
      for i = 1:nrows(C1)
        for j1 = 1 : ncols(C1)
          l = [i,j1]
          if C1[i,j1] == -2
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
      v_sR2 = deleteat!(copy(v_sR), l)
      l1 = (v_sR[l[1]] * transpose(v_sR[l[1]]))[1]
      l2 = (v_sR[l[2]] * transpose(v_sR[l[2]]))[1]
      l3 = (v_sR2[1] * transpose(v_sR2[1]))[1]
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
  return root_system_G
end

#R = root_system(:C, 30);
#n = num_simple_roots(R);
#S,l = root_system_type(R)[1];
#ro = [root(R, i).vec for i = 1:num_roots(R)];
#sr= findall(==(-2*(sum([ro[i] for i = 2:n-1]))-ro[1]-ro[n] ), ro)[1];
#v0 = vcat([r for r = 1:n-1], sr);
#v = [ro[v0[i]] for i = 1:length(v0)];
#V2 = VectorSpace(QQ, n);
#V1 = quadratic_space(QQ, n);
#E = identity_matrix(QQ, n);
#m0 = append!([V2(transpose(E[:, i ] - E[:, i+1])) for i = 1:n-1], [V2(transpose(2*E[:, n]))]);
#m0 = matrix(m0);
#m = transpose(m0);
#find_root_system_type(v, m0)
