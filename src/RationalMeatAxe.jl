module RationalMeatAxe

using Hecke
using Markdown

using Hecke: ModAlgHom
import Base: reshape

Mod = Hecke.ModAlgAss
AlgElem = Hecke.AlgAssElem{fmpq, AlgAss{fmpq}}

@doc Markdown.doc"""
    meataxe(M::Mod) -> Vector{Mod}

Given a semisimple module $M$ return simple submodules which add up to $M$.

The underlying algebra $A$ can be chosen as a subalgebra of $\operator{Mat}_N\mathbf Q$.
Implements algorithm by Allan Steel.
"""
function meataxe(M::Mod)
    reduce(vcat, split_homogeneous.(homogeneous_components(M)))
end

@doc Markdown.doc"""
    homogeneous_components(M::Mod) -> Vector{Mod}

Return homogeneous $S_i$ such that $M=\bigoplus_i S_i=M$.

The input $M$ needs to be semisimple. Homogeneous means to be isomorphic to a
direct sum of copies of some simple module.

See also [`split_homogeneous(::Mod)`](@ref).
"""
function homogeneous_components(M::Mod) :: Vector{Mod}
    z, zhom = center_of_endomorphism_ring(M)
    dim(z) == 1 && return [M]
    B = frommatrix(lll(saturate(asmatrix(matrix.(zhom.((basis(z))))))))
    for b in B
        f = minpoly(b)
        println(b,f)
        is_irreducible(f) && degree(f) == dim(z) && return [M]
        fs = factor(f)
        length(fs) == 1 && continue
        p, e = first(fs)
        f1 = p^e
        f2 = divexact(f, f1)
        ss1 = homogeneous_components(M, f1(b))
        ss2 = homogeneous_components(M, f2(b))
        return [ss1; ss2]
    end
    return [M]
end

function homogeneous_components(M::Mod, A::fmpz_mat) :: Vector{Mod}
    to, from = sub_morphisms(A)
    from.(homogeneous_components(to(M)))
end

function center_of_endomorphism_ring(M::Mod)
    endM, endMhom = Hecke.endomorphism_algebra(M)
    z, zhom = center(endM)
    return z, zhom * endMhom
end

fmpx_mat = Union{fmpz_mat, fmpq_mat}

function asmatrix(v::Vector{fmpq_mat}) :: fmpz_mat
    @assert !isempty(v)
    reduce(vcat, reshape.(numerator.(v), 1, :))
end
reshape(x::T, dims...) where T<:fmpx_mat = matrix(base_ring(x), reshape(Array(x), dims...)) :: T
numerator(a::fmpq_mat) = MatrixSpace(ZZ, size(a)...)(ZZ.(denominator(a)*a)) :: fmpz_mat

function frommatrix(x::T) :: Vector{T} where T <: fmpx_mat
    m, n_square = size(x)
    @assert m > 0
    n = exact_sqrt(n_square)
    collect(MatrixSpace(base_ring(x), n, n).(eachrow(x)))
end
Base.eachrow(x::fmpx_mat) = eachrow(Array(x))
exact_sqrt(n::Int) = Int(sqrt(ZZ(n)))

# Zeilen von `A` bzw. `H` sollen Submodul `N` von `M` erzeugen.
# mHx = mTAx = mTxA = mTxT⁻¹TA =mTxT⁻¹H
# Ist `M` durch Menge `X` von Matrizen erzeugt, so ist `N` durch
# { TxT⁻¹ : x∈X } erzeugt.
function sub_morphisms(A::fmpz_mat)
    m = size(A, 1)
    @assert m == size(A, 2)
    H, T = hnf_with_transform(A) # TA=H
    n = rank(H)
    @assert n < m
    return sub_morphisms(T, n, m)
end

function sub_morphisms(T::fmpz_mat, n::Int, m::Int)
    transform_matrix(x) = submatrix(conjugate(x, T), n)
    backtransform_matrix(x) = conjugate(embedmatrix(x, m), inv(T))
    to(M) = Amodule(transform_matrix.(Hecke.action_of_gens(M)))
    from(M) = Amodule(backtransform_matrix.(Hecke.action_of_gens(M)))
    return to, from
end

conjugate(a, t) = inv(t) * a * t

submatrix(A::fmpq_mat, n::Int) = (@assert is_submatrix(A, n); A[1:n, 1:n])

function is_submatrix(A::fmpq_mat, n::Int)
    A[:, n+1:end] == 0 && A[n+1:end, :] == 0 && return true
    show(A); show(n)
    false
end

function embedmatrix(A::fmpq_mat, m::Int)
    B = zero(MatrixSpace(QQ, m, m))
    n = size(A, 1)
    B[1:n, 1:n] = A
    B
end

# ===

@doc Markdown.doc"""
    split_homogeneous(M::Mod) -> Vector{Mod}

Return pairwise isomorphic simple $S_i$ such that $M=\bigoplus_i S_i=M$.

The input $M$ needs to be homogeneous, i.e. allow such a decomposition.

See also [`homogeneous_components(::Mod)`](@ref).
"""
function split_homogeneous(M::Mod)
    endM, endMhom = Hecke.endomorphism_algebra(M)
    o = maximal_order(endM)
    si = schur_index(endM)
    d = divexact(dim(endM), dim(center(endM)[1]))
    m = divexact(sqrt(d), si)
    m == 1 && return [M]
    s = maximal_order_basis_search(o)
    fs = factor(minpoly(s))
    @assert length(fs) > 1
    singularElements = (endMhom((p^e)(s)) for (p, e) in fs)
    return vcat(split_homogeneous.(kernel.(singularElements)))
end

function maximal_order_basis_search(v::Vector{AlgElem})
    (a = find(is_split, v)) !== nothing && return a
    for b1 in v, b2 in v
        is_split(b1 * b2) && return b1 * b2
        is_split(b1 + b2) && return b1 + b2
    end
    while a === nothing
        a = find(is_split, lll(rand(v) * rand(v) for _ in eachindex(v)))
    end
    return a
end

find(f, v) = (i = findfirst(f, v); i === nothing ? nothing : f[i])

is_split(a::AlgElem) = !is_irreducible(minpoly(a))

end
