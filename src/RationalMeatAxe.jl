module RationalMeatAxe

using Hecke

using Hecke: ModAlgHom
import Base: reshape
import Hecke: sub, domain, codomain, mat

include("RandomAlgebras.jl")

__init__() = Hecke.add_verbosity_scope(:rma)

Mod = Hecke.ModAlgAss
AlgElem = Hecke.AlgAssElem{QQFieldElem, AlgAss{QQFieldElem}}

# TODO: Hecke.decompose anschauen, oder gleich ganz Hecke.AlgAss

@doc raw"""
    meataxe(M::Mod) -> Vector{Mod}

Given a semisimple module $M$ return simple submodules which add up to $M$.

The underlying algebra $A$ can be chosen as a subalgebra of $\operator{Mat}_N\mathbf Q$.
Implements algorithm by Allan Steel.
"""
function meataxe(M::Mod)
    reduce(vcat, split_homogeneous.(homogeneous_components(M)))
end

@doc raw"""
    homogeneous_components(M::Mod) -> Vector{Mod}

Return homogeneous $S_i$ such that $M=\bigoplus_i S_i=M$.

The input $M$ needs to be semisimple. Homogeneous means to be isomorphic to a
direct sum of copies of some simple module.

See also [`split_homogeneous(::Mod)`](@ref).
"""
function homogeneous_components(M::Mod) :: Vector{Mod}
    @vprint :rma "# Homogeneous Components of $M\n"
    B = basis_of_center_of_endomorphism_ring(M)
    B === nothing && return [M]
    dim_of_center = length(B)
    QQx, x = polynomial_ring(QQ, :x)
    @vprint :rma "## Iterating through basis $B of the center of the endomorphism ring\n"
    for b in B
        @vprint :rma "Current basis element is\n"
        @v_do :rma display(b)
        f = minpoly(b)
        is_irreducible(f) && degree(f) == dim_of_center && return [M]
        fs = factor(f)
        length(fs) == 1 && continue
        p, e = first(fs)
        f1 = p^e
        f2 = divexact(f, f1)
        @vprint :rma "Minimal polynomial is $f with coprime factors $f1 and $f2\n"
        f1, f2 = QQx(f1), QQx(f2)
        _1, s, t = gcdx(f1, f2)
        f1, f2 = s*f1, t*f2
        @vprint :rma "Using multiples $f1 and $f2 summing up to 1\n"
        @assert _1 == 1
        ss1 = homogeneous_components(M, f1(QQMatrix(b)))
        ss2 = homogeneous_components(M, f2(QQMatrix(b)))
        return [ss1; ss2]
    end
    return [M]
end

function homogeneous_components(M::Mod, A::QQMatrix) :: Vector{Mod}
    @vprint :rma "### Splitting at\n"
    @v_do :rma display(A)
    MA = sub(M, A)
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

raw"""
    ModHom(M::Hecke.ModAlgAss, A::Mat)

Module automorphism from $M$ to $M⋅T$, where $AT=H$ is the HNF of $A$.
"""
struct ModHom
    rank :: Int
    T :: Mat
    invT :: Mat
    domain :: Hecke.ModAlgAss
    # Sei 𝓐 ⊆ K^{𝑚×𝑚} K-rechts-Algebra, jedes X∈𝓐 also auf dem Modul $M=K^𝑚$
    # von rechts operierende Matrix.
    # Ferner sei A∈End_K(𝓐), also AX=XA und H=AT die Spalten-HNF von A mit 𝑛 nicht-null-Spalten.
    # Vermittels des Isomorphismus M⋅A → M⋅H=M⋅AT, m ↦ mT operiert X auf m∈M⋅H als mT⁻¹XT.
    # Nun hat HT⁻¹XT = AXT = XAT = XH ebenfalls nur n nicht-null-Spalten, ist also von der Form
    # (m×n)   0.
    function ModHom(domain::Hecke.ModAlgAss, A::Mat)
        H, T = hnf_with_transform(transpose(A))
        T = transpose!(T)
        return new(Hecke.rank_of_ref(H), T, inv(T), domain)
    end
end
domain(a::ModHom) = a.domain
codomain(a::ModHom) = image(a, a.domain)
mat(a::ModHom) = a.T
image(h::ModHom, x::Mat) = submatrix(h.invT * x * h.T, h.rank)
image(h::ModHom, M::Mod) = Amodule(image.((h,), Hecke.action_of_gens(M)))

struct SubMod
    M :: Hecke.ModAlgAss
    hom :: ModHom
    SubMod(h::ModHom) = new(codomain(h), h)
end
SubMod(M::Hecke.ModAlgAss, A::Mat) = SubMod(ModHom(M, A))
sub(M::Hecke.ModAlgAss, A::Mat) = codomain(ModHom(M, A))

ModHom(a::Hecke.ModAlgHom) = ModHom(domain(a), matrix(a))
sub(a::Hecke.ModAlgHom) = codomain(ModHom(a))


# TᵀAᵀ = Hᵀ ⇔ (AT)ᵀ = Hᵀ ⇔ AT = H
column_hnf_with_transform(A) = transpose.(hnf_with_transform(transpose(A)))

submatrix(A::QQMatrix, n::Int) = (@assert A[1:n, n+1:end] == 0; A[1:n, 1:n])


function embedmatrix(A::QQMatrix, m::Int)
    B = zero(MatrixSpace(QQ, m, m))
    n = size(A, 1)
    B[1:n, 1:n] = A
    B
end

# ===

@doc raw"""
    split_homogeneous(M::Mod) -> Vector{Mod}

Return pairwise isomorphic simple $S_i$ such that $M=\bigoplus_i S_i=M$.

The input $M$ needs to be homogeneous, i.e. allow such a decomposition.

See also [`homogeneous_components(::Mod)`](@ref).
"""
function split_homogeneous(M::Mod)
    endM, endM_to_actual_endM = Hecke.endomorphism_algebra(M)
    endMAA, endMAA_to_endM = AlgAss(endM)
    A, A_to_endMAA = Hecke._as_algebra_over_center(endMAA)
    A_to_endM = A_to_endMAA * endMAA_to_endM
    # Note: `schur_index(A)` computes maximal_order(A), which takes some time.
    # Actually, it may take much longer than maximal_order(endM). Why?
    # Can we use maximal_order(endM) instead?
    # TODO: @profile maximal_order(A) for our example transitive group.
    dim(A) == schur_index(A)^2 && return [M]
    v = first.(pseudo_basis(maximal_order(A)))
    s = basis_search(A_to_endM, v)
    # TODO: Somehow reuse existing structure information, ie
    # maximal_order and possibly multiplication table
    # s_inA = maximal_order_basis_search(maximal_order(A), A_to_endM)
    # s = endMAA_to_endM(A_to_endMAA(s_inA))
    # s = maximal_order_basis_search(endM)
    fs = factor(minpoly(s))
    @assert length(fs) > 1
    singularElements = (endM_to_actual_endM((p^e)(s)) for (p, e) in fs)
    return reduce(vcat, split_homogeneous.(sub.(singularElements)))
end

Hecke.kernel(a::Hecke.ModAlgHom) = sub(domain(a), kernel(matrix(a))[2])

# basis_search(v::Vector) = find(is_split, Iterators.flatten(
#     _repeat_last(_pairwise_sums, _pairwise_products, _lll_random_elements) .|> (v,)))
# _repeat_last(args...) = Iterators.flatten((args[1:end-1], Iterators.repeated(args[end])))
# _lll_random_elements(v::Vector) = lll_saturate([x*rand(v) for x in v])

function basis_search(toAlgMat::Map, v::Vector)
    (a = find(is_split, v)) === nothing || (@vprintln :rma "Split directly"; return toAlgMat(a))
    (a = find(is_split, _pairwise_sums(v))) === nothing || (@vprintln :rma "Split at sum"; return toAlgMat(a))
    (a = find(is_split, _pairwise_products(v))) === nothing || (@vprintln :rma "Split at product"; return toAlgMat(a))
    @vprintln :rma "lll-saturating basis"
    return basis_search(toAlgMat.(v))
end
function basis_search(v::Vector)
    v1 = v
    while !isempty(v1)
        (a = find(is_split, v1)) === nothing || (@vprintln :rma "Split directly"; return a)
        (a = find(is_split, _pairwise_sums(v1))) === nothing || (@vprintln :rma "Split at sum"; return a)
        (a = find(is_split, _pairwise_products(v1))) === nothing || (@vprintln :rma "Split at product"; return a)
        v2 = permutedims(setdiff(v, v1))
        (a = find(is_split, v1 .+ v2)) === nothing || (@vprintln :rma "Split at sum with old"; return a)
        (a = find(is_split, v1 .* v2)) === nothing || (@vprintln :rma "Split at product with old"; return a)
        (a = find(is_split, v2 .* v1)) === nothing || (@vprintln :rma "Split at product with old"; return a)
        @vprintln :rma "lll-saturating enlarged basis"
        v0 = lll_saturate([v; [rand(v)*rand(v) for _ in v]])
        v, v1  = v0, setdiff(v0, v)
    end
    @vprintln :rma "brutally lll-saturating enlarged basis"
    vv = collect(Iterators.flatten((v, _pairwise_products(v))))
    v0 = lll_saturate(vv)
    v, v1  = v0, setdiff(v0, v)
    while !isempty(v1)
        (a = find(is_split, v1)) === nothing || (@vprintln :rma "Split directly"; return a)
        (a = find(is_split, _pairwise_sums(v1))) === nothing || (@vprintln :rma "Split at sum"; return a)
        (a = find(is_split, _pairwise_products(v1))) === nothing || (@vprintln :rma "Split at product"; return a)
        v2 = permutedims(setdiff(v, v1))
        (a = find(is_split, v1 .+ v2)) === nothing || (@vprintln :rma "Split at sum with old"; return a)
        (a = find(is_split, v1 .* v2)) === nothing || (@vprintln :rma "Split at product with old"; return a)
        (a = find(is_split, v2 .* v1)) === nothing || (@vprintln :rma "Split at product with old"; return a)
        @vprintln :rma "brutally lll-saturating enlarged basis"
        vv = collect(Iterators.flatten((v, _pairwise_products(v))))
        v0 = lll_saturate(vv)
        v, v1  = v0, setdiff(v0, v)
    end
    @vprintln :rma "lll-saturating randomized basis"
    while true
        @vprint :rma '.'
        v1 = lll_saturate([x*rand(v)*rand(v) for x in v])
        (a = find(is_split, v1)) === nothing || (@vprintln :rma "Split directly"; return a)
        (a = find(is_split, _pairwise_sums(v1))) === nothing || (@vprintln :rma "Split at sum"; return a)
        (a = find(is_split, _pairwise_products(v1))) === nothing || (@vprintln :rma "Split at product"; return a)
    end
end

_pairwise_sums(v::Vector) = (x+y for (i,x) in enumerate(v) for y in v[i:end])
_pairwise_products(v::Vector) = (x*y for x in v, y in v)

find(f, v) = for x in v f(x) && return x end

is_split(a) = length(factor(minpoly(a))) > 1

end
