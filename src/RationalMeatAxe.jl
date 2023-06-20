module RationalMeatAxe

using Hecke

using Hecke: ModAlgHom
import Base: reshape
import Hecke: sub, domain, codomain, mat

include("SubModules.jl")
include("RandomAlgebras.jl")

__init__() = Hecke.add_verbosity_scope(:rma)

Mod = Hecke.ModAlgAss
AlgElem = Hecke.AlgAssElem{QQFieldElem, AlgAss{QQFieldElem}}

@doc raw"""
    meataxe(M::AbstractSubModule) -> Vector{AbstractSubModule}

Given a semisimple module $M$ return simple submodules which add up to $M$.

The underlying algebra $A$ can be chosen as a subalgebra of $\operator{Mat}_N\mathbf Q$.
Implements algorithm by Allan Steel.
"""
function meataxe(M::AbstractSubModule)
    @vprintln :rma "# Splitting into homogeneous components ..."
    Hecke.pushindent()
    Mhomos = homogeneous_components(M)
    Hecke.popindent()
    @vprintln :rma "---\n# Splitting homogeneous components ..."
    Hecke.pushindent()
    Msimples = reduce(vcat, split_homogeneous.(Mhomos))
    Hecke.popindent()
    return Msimples
end

meataxe(M::Mod) = codomain.(meataxe(ThisModule(M)))
homogeneous_components(M::Mod) = codomain.(homogeneous_components(ThisModule(M)))
split_homogeneous(M::Mod) = codomain.(split_homogeneous(ThisModule(M)))

@doc raw"""
    homogeneous_components(M::AbstractSubModule) -> Vector{AbstractSubModule}

Return homogeneous $S_i$ such that $M=\bigoplus_i S_i=M$.

The input $M$ needs to be semisimple. Homogeneous means to be isomorphic to a
direct sum of copies of some simple module.

See also [`split_homogeneous(::AbstractSubModule)`](@ref).
"""
function homogeneous_components(M::AbstractSubModule) :: Vector{AbstractSubModule}
    @vprintln :rma "# Homogeneous Components of $M"
    B = basis_of_center_of_endomorphism_ring(codomain(M))
    dim_of_center = length(B)
    QQx, x = polynomial_ring(QQ, :x)
    @vprintln :rma "## Iterating through basis $B of the center of the endomorphism ring"
    for b in B
        @vprintln :rma 2 "Current basis element is"
        @v_do :rma 2 display(b)
        f = minpoly(b)
        is_irreducible(f) && degree(f) == dim_of_center && break
        fs = factor(f)
        length(fs) == 1 && continue
        codomain(M).is_irreducible = FALSE
        p, e = first(fs) # TODO: can we take all factors instead?
        f1 = p^e
        f2 = divexact(f, f1)
        @vprintln :rma "Minimal polynomial is $f with coprime factors $f1 and $f2"
        f1, f2 = QQx(f1), QQx(f2)
        _1, s, t = gcdx(f1, f2)
        f1, f2 = s*f1, t*f2
        @vprintln :rma "Using multiples $f1 and $f2 summing up to 1"
        @assert _1 == 1
        ss1 = homogeneous_components(M, f1(QQMatrix(b)))
        ss2 = homogeneous_components(M, f2(QQMatrix(b)))
        return [ss1; ss2]
    end
    codomain(M).is_irreducible = TRUE
    return [M]
end

function homogeneous_components(M::AbstractSubModule, A::QQMatrix) :: Vector{AbstractSubModule}
    @vprintln :rma 2 "### Splitting at"
    @v_do :rma 2 display(A)
    MA = SubModule(M, A)
    Hecke.pushindent()
    L = homogeneous_components(MA)
    Hecke.popindent()
    return L
end

basis_of_center_of_endomorphism_ring(M::Mod) = lll_saturate(center_of_endomorphism_ring(M))

# TODO improve this
# 1. build up modularly
# 2. make modular case clever
center_of_endomorphism_ring(M::Mod) = naive_center_of_endomorphism_ring(M)
function naive_center_of_endomorphism_ring(M::Mod)
    endM, endMhom = Hecke.endomorphism_algebra(M)
    z, zhom = center(endM)
    return numerator.(matrix.(endMhom.(zhom.(basis(z)))))
end

Mat = Union{ZZMatrix, QQMatrix}

Hecke.lll(a::Vector{ZZMatrix}) = isempty(a) ? a : frommatrix(lll(asmatrix(a)), size(a[1])...)
lll_saturate(a::Vector{ZZMatrix}) = isempty(a) ? a : frommatrix(lll(saturate(asmatrix(a))), size(a[1])...)
lll_saturate(a::Vector{QQMatrix}) = QQMatrix.(lll_saturate(numerator.(a)))
lll_saturate(v::Vector{T}) where T<:NCRingElem = isempty(v) ? v : parent(v[1]).(lll_saturate(matrix.(v))) :: Vector{T}
lll_saturate(v::Vector{T}) where T<:AlgAssElem = isempty(v) ? v : parent(v[1]).(lll_saturate(matrix.(v))) :: Vector{T}


asmatrix(v::Vector{T}) where T <: MatElem = reduce(vcat, newshape.(v, 1, :)) :: T

frommatrix(a::T, r::Int, c::Int) where T <: MatElem = T[newshape(x, r, c) for x in eachrow(a)]

newshape(a::MatElem, dims::Union{Int, Colon}...) = newshape(a, dims)
newshape(a::MatElem, dims::NTuple{2, Union{Int, Colon}}) = newshape(a, Base._reshape_uncolon(a, dims))

# Iterate column wise, probably somewhat inefficient, as flint stores matrices rowwise.
function newshape(a::T, dims::NTuple{2, Int}) ::T where T<:MatElem
    b = similar(a, dims...)
    for (I, x) in zip(CartesianIndices(dims), a)
        b[I] = x
    end
    return b
end

Base.eachrow(a::MatElem) = (view(a, i, :) for i in axes(a, 1))
Base.eachcol(a::MatElem) = (view(a, :, i) for i in axes(a, 2))

numerator(a::QQMatrix) = MatrixSpace(ZZ, size(a)...)(ZZ.(denominator(a)*a)) :: ZZMatrix


# ===

@doc raw"""
    split_homogeneous(M::AbstractSubModule) -> Vector{AbstractSubModule}

Return pairwise isomorphic simple $S_i$ such that $M=\bigoplus_i S_i=M$.

The input $M$ needs to be homogeneous, i.e. allow such a decomposition.

See also [`homogeneous_components(::AbstractSubModule)`](@ref).
"""
function split_homogeneous(M::AbstractSubModule) :: Vector{AbstractSubModule}
    @vprint :rma "Splitting Homogeneous $M"
    endM, endM_to_actual_endM = Hecke.endomorphism_algebra(codomain(M)) # already known from basis_of_center_of_endomorphism_ring when we come from `meataxe`
    endMAA, endMAA_to_endM = AlgAss(endM) # TODO: Takes forever for M=Amodule(identity_matrix(QQ,8)) 😟
    A, A_to_endMAA = Hecke._as_algebra_over_center(endMAA)
    A_to_endM = A_to_endMAA * endMAA_to_endM
    dim(A) == schur_index(A)^2 && (@vprintln :rma "is trivial"; codomain(M).is_irreducible = TRUE; return [M])
    codomain(M).is_irreducible = FALSE
    v = first.(pseudo_basis(maximal_order(A)))
    @vprintln :rma "by searching in $v"
    s = basis_search(A_to_endM, v)
    fs = factor(minpoly(s))
    @assert length(fs) > 1
    singularElements = (endM_to_actual_endM((p^e)(s)) for (p, e) in fs)
    return reduce(vcat, split_homogeneous.(SubModule.((M,), singularElements)))
end

"""
    basis_search(toAlgMat::Map=identity, v::Vector)

Split element in `toAlgMat.(v)`.
First try elements of `v` and sums and products, then try more fancy stuff.
"""
basis_search(toAlgMat::Map, v::Vector) =
    (a = direct_basis_search(v)) !== nothing ? toAlgMat(a) : _basis_search(toAlgMat.(v))

basis_search(v::Vector) =
    (a = direct_basis_search(v)) !== nothing ? a : _basis_search(v)

function direct_basis_search(v::Vector{T}) :: Union{T, Nothing} where T
    (a = find(is_split, v)) === nothing || (@vprintln :rma "Splits directly"; return a)
    (a = find(is_split, _pairwise_sums(v))) === nothing || (@vprintln :rma "Splits at sum"; return a)
    (a = find(is_split, _pairwise_products(v))) === nothing || (@vprintln :rma "Splits at product"; return a)
    return nothing
end
_pairwise_sums(v::Vector) = (x+y for (i,x) in enumerate(v) for y in v[i:end])
_pairwise_products(v::Vector) = (x*y for x in v, y in v)

"""
    _basis_search(v::Vector{T}) -> :: T

Complicated search for split elements using hopefully clever techniques.
"""
function _basis_search(v::Vector)
    @vprintln :rma "Working with and lll-saturating $v"
    a = false
    while a === false
        @vprintln :rma "lll-saturating enlarged basis"
        # Caveat: actually we had a basis over the center, thus it can now become uselessly large
        new = lll_saturate([v; [rand(v)*rand(v) for _ in v]])
        a = basis_search_with_old(new, v)
        v = new
    end
    a === true || return a
    a = false
    while a === false
        @vprintln :rma "brutally lll-saturating enlarged basis"
        vv = collect(Iterators.flatten((v, _pairwise_products(v))))
        new = lll_saturate(vv)
        a = basis_search_with_old(new, v)
        v = new
    end
    a === true || return a
    s = nothing
    @vprintln :rma "lll-saturating randomized basis $v"
    while s === nothing
        @vprint :rma '.'
        new = lll_saturate([x*rand(v)*rand(v) for x in v])
        s = direct_basis_search(new)
    end
    @vprintln :rma "found $s"
    return s
end
"""
    basis_search_with_old(v::Vector, old::Vector) -> Union{Bool,T}

Search for split elements using `v`, and combinations of `v` and `old`.
Return it, or if none found, return `v==old`.
"""
function basis_search_with_old(v::Vector{T}, old::Vector{T}) :: Union{Bool,T} where T
    new = setdiff(v, old)
    isempty(new) && return true
    (a = direct_basis_search(new)) === nothing || return a
    w = permutedims(setdiff(old, v))
    (a = find(is_split, new .+ w)) === nothing || (@vprintln :rma "Splits at sum with old"; return a)
    (a = find(is_split, new .* w)) === nothing || (@vprintln :rma "Splits at product with old"; return a)
    (a = find(is_split, w .* new)) === nothing || (@vprintln :rma "Splits at product with old"; return a)
    return false
end

find(f, v) = for x in v f(x) && return x end

is_split(a) = length(factor(minpoly(a))) > 1

### Module fun

function Base.:+(V::Hecke.ModAlgAss{KK,MM,AA}, W::Hecke.ModAlgAss{KK,MM,AA}) where {KK,MM<:MatrixElem,AA}
    actionV, actionW = Hecke.consistent_action(V, W)
    dim(W) == 0 && return V
    dim(V) == 0 && return W
    actionVW = block_diagonal_matrix.([v, w] for (v, w) in zip(actionV, actionW))
    VW = Hecke.has_algebra(V) ?
        isdefined(V, :action_of_gens) && isdefined(W, :action_of_gens) ?
            Hecke.ModAlgAss{MM,AA}(algebra(V); action_of_gens=actionVW) :
            Hecke.ModAlgAss{MM,AA}(algebra(V); action_of_basis=actionVW) :
        Hecke.ModAlgAss{MM}(; action_of_gens=actionVW)
    if isdefined(V, :action_of_gens_inverse) && isdefined(W, :action_of_gens_inverse)
        VW.action_of_gens_inverse = block_diagonal_matrix.([v, w] for (v, w) in zip(V.action_of_gens_inverse, W.action_of_gens_inverse))
    end
    VW.is_irreducible = 1
    VW.is_abs_irreducible = 1
    return VW
end

const UNKNOWN = 0
const TRUE = 1
const FALSE = 2

end
