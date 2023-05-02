"""
    RandomAlgebras

Create algebras as their regular module.
"""
module RandomAlgebras

using RandomExtensions

sum_of_matrix_algebras = Amodule ∘ change_basis ∘ sum_of_matrix_algebras_gens

raw"""
    sum_of_matrix_algebras_gens(...)

$⨁_{i=1}^n A_i$ where the $A_i$ are some matrix algebras with `max_size ×
max_size` matrices.
"""
function sum_of_matrix_algebras_gens(R, number, max_size, max_gens, max_num)
    sizes = rand(1:max_size, number)
    offsets = cumsum(sizes)
    N = offsets[end]
    gss = [enlarge_matrix.(rand_gens(R, n, n, max_num), N, o) for (n,o) in zip(sizes,offsets)]
    return reduce(vcat, gss)
end

"""
    change_basis(matrices)

Change with some random basis.
"""
function change_basis(matrices)
    if isempty(matrices) return matrices
    n = size(matrices[1], 1)
    for m in matrices @assert size(m) == (n, n)

    M = MatrixAlgebra(eltype(matrices), n)
    C = rand_invertible(M)

    return [inv(C)*M(m)*C for m in matrices]
end

function rand_invertible(R, v...)
    while x = rand(R) |> !is_invertible end
    return x
end

raw"""
    rand_gens(R, n, ngens, max_num=9)

Some module generators, i.e. `ngens` julia matrices from $R^{n×n}$ with
absolute value of entries up to `max_num`.
"""
rand_gens(R, n, ngens, max_num) = eachslice(rand(make(R, -max_num:max_num), n, n, ngens); dims=3)

raw"""
    enlarge_matrix(A, n=size(A,1), end_offset=size(A,1))

Turn $m×m$ matrix $A$ into a $n×n$ matrix by placing it at offset on the diagonal.
"""
function enlarge_matrix(A::Array{T}, n=size(A, 1), end_offset=size(A, 1)) where T<:NCRingElem
    @assert size(A, 1) == size(A, 2)
    m = size(A, 1)
    B = zeros(T, n, n)
    new_pos = end_offset-m+1 : end_offset
    B[new_pos, new_pos] = A
    return B
end

end

