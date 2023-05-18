"""
    RandomAlgebras

Create algebras as their regular module.
"""
module RandomAlgebras

using RandomExtensions
using Hecke

rand_sum_of_matrix_algebras(entries, args...) =
    Amodule(rand_change_basis(entries,
        rand_sum_of_matrix_algebras_gens(entries, args...)))

raw"""
    sum_of_matrix_algebras_gens(entries, number, max_size, max_gens)

$⨁_{i=1}^n A_i$ where the $A_i$ are some matrix algebras with matrices up to `max_size` and entries randomly taken from `entries`.

# Examples

```jldoctest
julia> sum_of_matrix_algebras_gens(make(ZZ, -9:9), 2, 3, 5)
// up to 10 block diagonal matrices with two blocks each of size up to 3 and only one non-zero block.

```
"""
rand_sum_of_matrix_algebras_gens(entries, number, max_size, max_gens) =
    rand_sum_of_matrix_algebras_gens(
        entries, rand(make(Pair, 1:max_size, 1:max_gens), number))

function rand_sum_of_matrix_algebras_gens(entries, sizes_and_amount::Vector{Pair{Int, Int}})
    offsets = cumsum(first.(sizes_and_amount))
    ranges = [a+1:b for (a,b) in zip([0;offsets[1:end-1]], offsets)]
    ranges_and_amount = (r => a for (r, (_, a)) in zip(ranges, sizes_and_amount))
    return rand_sum_of_matrix_algebras_gens(entries, ranges_and_amount, offsets[end])
end

rand_sum_of_matrix_algebras_gens(
        entries, ranges_and_amount, total_size::Int) =
    [rand_mat(entries, r, total_size) for (r, a) in ranges_and_amount for _ in 1:a]

"""
    rand_change_basis(matrices)

Change with some random basis.
"""
function rand_change_basis(entries, matrices)
    isempty(matrices) && return matrices
    matrices = matrices
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
    rand_mat(entries, position::UnitRange{Int}, n::Int) -> Matrix{eltype(entries)}

Some $n×n$ matrix `A` with random entries in `A[position, position]` and zero everywhere else.
"""
function rand_mat(entries, position::UnitRange{Int}, n::Int)
    A = zeros(eltype(entries), n, n)
    A[position, position] = rand(entries, length(position), length(position))
    return A
end

end
