"""
    RandomAlgebras

Create algebras as their regular module.
"""
module RandomAlgebras

using RandomExtensions
using Hecke

rand_sum_of_matrix_algebras(R, entries, args...) =
    Amodule(rand_change_basis(make(R, entries),
        sum_of_matrix_algebras_gens(R, args...)))

raw"""
    sum_of_matrix_algebras_gens(R, sizes::Vector{Int})

Two matrices generating an algebra, which contains one subalgebra isomorphic to the algebra of $n\times n$-matrices for each `n` in `sizes`.

# Examples

```jldoctest
julia> A, B = sum_of_matrix_algebras_gens(QQ, [1, 1, 2, 3]); A
[1   0   0   0   0   0   0]
[0   1   0   0   0   0   0]
[0   0   1   0   0   0   0]
[0   0   0   0   0   0   0]
[0   0   0   0   1   0   0]
[0   0   0   0   0   0   0]
[0   0   0   0   0   0   0]

julia> B
[1   0   0   0   0   0   0]
[0   1   0   0   0   0   0]
[0   0   0   1   0   0   0]
[0   0   1   0   0   0   0]
[0   0   0   0   0   1   0]
[0   0   0   0   0   0   1]
[0   0   0   0   1   0   0]

```
"""
function sum_of_matrix_algebras_gens(R, sizes::Vector{<:Pair{Int}})
    filter!(((x, y),) -> x > 0, sizes)
    isempty(sizes) && return matrix(R, [;;]), matrix(R, [;;])
    As = [(A = zero_matrix(R, n, n); A[1, 1] = a; A) for (n, a) in sizes]
    Bs = [identity_matrix(R, n)[[2:end; begin], :] for (n, _) in sizes]
    return block_diagonal_matrix(As), block_diagonal_matrix(Bs)
end

sum_of_matrix_algebras_gens(R, sizes) = sum_of_matrix_algebras_gens(R, _to_pairs.(sizes, [one(R)]))
_to_pairs(a::Pair, defaultvalue) = a
_to_pairs(a, defaultvalue) = a => defaultvalue

"""
    rand_change_basis(matrices)

Change with some random basis.
"""
function rand_change_basis(entries, matrices)
    isempty(matrices) && return matrices
    n = size(matrices[1], 1)
    for m in matrices @assert size(m) == (n, n) end
    n == 0 && return matrices

    R = parent(matrices[1][1, 1])
    M = MatrixSpace(R, n, n)
    C = rand_invertible(make(M, entries))

    return [inv(C)*M(m)*C for m in matrices]
end

function rand_invertible(R)
    while (x = rand(R)) |> !is_invertible end
    return x
end

end
