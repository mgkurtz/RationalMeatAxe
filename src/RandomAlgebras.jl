"""
    RandomAlgebras

Create algebras as their regular module.
"""
module RandomAlgebras

using RandomExtensions
using Hecke

rand_sum_of_matrix_algebras(entries, number, max_size, max_gens) =
    Amodule(rand_change_basis(entries,
        rand_sum_of_matrix_algebras_gens(entries, number, max_size, max_gens)))

raw"""
    sum_of_matrix_algebras_gens(entries, number, max_size, max_gens)

$⨁_{i=1}^n A_i$ where the $A_i$ are some matrix algebras with matrices up to `max_size` and entries randomly taken from `entries`.

# Examples

```jldoctest
julia> sum_of_matrix_algebras_gens(make(ZZ, -9:9), 2, 3, 5)
// up to 10 block diagonal matrices with two blocks each of size up to 3 and only one non-zero block.

```
"""
function rand_sum_of_matrix_algebras_gens(entries, number, max_size, max_gens)
    sizes = rand(1:max_size, number)
    offsets = cumsum(sizes)
    N = offsets[end]
    ngens = rand(1:max_gens, number)
    gss = [enlarge_matrix.(rand_gens(entries, n, g), N, o) for (n,g,o) in zip(sizes,ngens,offsets)]
    return reduce(vcat, gss)
end

"""
    rand_change_basis(matrices)

Change with some random basis.
"""
function rand_change_basis(entries, matrices)
    isempty(matrices) && return matrices
    n = size(matrices[1], 1)
    for m in matrices @assert size(m) == (n, n) end
    n == 0 && return matrices

    R = parent(matrices[1][1])
    M = MatrixSpace(R, n, n)
    C = rand_invertible(make(M, entries))

    return [inv(C)*M(m)*C for m in matrices]
end

function rand_invertible(R)
    while (x = rand(R)) |> !is_invertible end
    return x
end

raw"""
    rand_gens(entries, n, ngens) -> iterator of Matrix{eltype(entries)}

Some module generators, i.e. `ngens` julia $n×n$ matrices with entries taken randomly from `entries`.
"""
rand_gens(entries, n, ngens) = eachslice(rand(entries, n, n, ngens); dims=3)

raw"""
    enlarge_matrix(A, n=size(A,1), end_offset=size(A,1)) -> Matrix{eltype(A)}

Turn $m×m$ matrix $A$ into a $n×n$ matrix by placing it at offset on the diagonal.
"""
function enlarge_matrix(A, n=size(A, 1), end_offset=size(A, 1))
    @assert size(A, 1) == size(A, 2)
    m = size(A, 1)
    B = zeros(eltype(A), n, n)
    new_pos = end_offset-m+1 : end_offset
    B[new_pos, new_pos] = A
    return B
end

end
