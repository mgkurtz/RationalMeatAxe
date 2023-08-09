_offsets(v) = UnitRange{Int}[e-l+1:e for (l,e) in zip(v, cumsum(v))]
function _block_one_matrix(R, n::Int, r::AbstractUnitRange{Int})
    a, e = first(r), last(r)
    return block_diagonal_matrix([
        zero_matrix(R, a-1, a-1),
        identity_matrix(R, e-a+1),
        zero_matrix(R, n-e, n-e)
   ])
end

