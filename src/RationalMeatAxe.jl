module RationalMeatAxe

using Hecke
using Markdown

using Hecke: ModAlgHom
import Base: reshape

Mod = Hecke.ModAlgAss
AlgElem = Hecke.AlgAssElem{fmpq, AlgAss{fmpq}}

__init__() = Hecke.add_verbosity_scope(:rma)

# TODO: Hecke.decompose anschauen, oder gleich ganz Hecke.AlgAss

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
    @vprint :rma "# Homogeneous Components of $M\n"
    z, zhom = center_of_endomorphism_ring(M)
    dim(z) == 1 && return [M]
    # TODO: Write this code using lattices
    B = frommatrix(lll(saturate(asmatrix(matrix.(zhom.((basis(z))))))))
    @vprint :rma "## Iterating through basis $B of the center of the endomorphism ring\n"
    for b in B
        @vprint :rma "Current basis element is\n"
        @v_do :rma display(b)
        f = minpoly(b)
        is_irreducible(f) && degree(f) == dim(z) && return [M]
        fs = factor(f)
        length(fs) == 1 && continue
        p, e = first(fs)
        f1 = p^e
        f2 = divexact(f, f1)
        @vprint :rma "Minimal polynomial is $f with coprime factors $f1 and $f2\n"
        ss1 = homogeneous_components(M, f1(b))
        ss2 = homogeneous_components(M, f2(b))
        return [ss1; ss2]
    end
    return [M]
end

function homogeneous_components(M::Mod, A::fmpz_mat) :: Vector{Mod}
    @vprint :rma "### Splitting at\n"
    @v_do :rma display(A)
    to, from = sub_morphisms(A)
    Hecke.pushindent()
    L = from.(homogeneous_components(to(M)))
    Hecke.popindent()
    return L
end

function center_of_endomorphism_ring(M::Mod)
    endM, endMhom = Hecke.endomorphism_algebra(M)
    z, zhom = center(endM)
    return z, zhom * endMhom
end

fmpx_mat = Union{fmpz_mat, fmpq_mat}

function asmatrix(v::Vector{fmpq_mat}) :: fmpz_mat
    @req !isempty(v) "Vector must be non-empty"
    return reduce(vcat, reshape.(numerator.(v), 1, :))
end
reshape(x::T, dims...) where T<:fmpx_mat = matrix(base_ring(x), reshape(Array(x), dims...)) :: T
numerator(a::fmpq_mat) = MatrixSpace(ZZ, size(a)...)(ZZ.(denominator(a)*a)) :: fmpz_mat

function frommatrix(x::T) :: Vector{T} where T <: fmpx_mat
    m, n_square = size(x)
    @assert m > 0
    n = exact_sqrt(n_square)
    return collect(MatrixSpace(base_ring(x), n, n).(eachrow(x)))
end
Base.eachrow(x::fmpx_mat) = eachrow(Array(x))
exact_sqrt(n::Int) = Int(sqrt(ZZ(n)))

# Sei 𝓐 ⊆ K^{𝑚×𝑚} K-rechts-Algebra, also X∈𝓐 auf dem Modul $M=K^𝑚$ von rechts operierende Matrix.
# Ferner sei A∈Z(𝓐) und H=AT die Spalten-HNF von A mit 𝑛 nicht-null-Spalten
# So operiert X∈𝓐 auf dem Submodul M⋅H = M⋅AT ≅ M⋅A
# wegen m ↦ mT⁻¹ entsprechend als m * X = mT⁻¹XT
# Da M⋅H=⨁_{i=1…n}Keᵢ≅Kⁿ Submodul ist, bildet X den Kⁿ auf sich selbst ab, T⁻¹XT ist also von der Form
# (n×n)   0
# (k×n) (k×k)
# mit 𝑘=𝑚−𝑛.
function sub_morphisms(A::fmpz_mat)
    m = size(A, 1)
    @assert m == size(A, 2)
    H, T = column_hnf_with_transform(A) # AT=H
    @vprint :rma "$A ⋅ $T = $H with T⁻¹=$(inv(T))\n"
    n = rank(H)
    @assert n < m
    return sub_morphisms(T, n, m)
end

# TᵀAᵀ = Hᵀ ⇔ (AT)ᵀ = Hᵀ ⇔ AT = H
column_hnf_with_transform(A) = transpose.(hnf_with_transform(transpose(A)))

function sub_morphisms(T::fmpz_mat, n::Int, m::Int)
    transform_matrix(x) = submatrix(right_conjugate(x, T), n)
    #TODO: Geht `embedmatrix` überhaupt? Wohl kaum, schließlich müssen wir wieder in unserem Modul rauskommen.
    backtransform_matrix(x) = left_conjugate(embedmatrix(x, m), T)
    to(M) = Amodule(transform_matrix.(Hecke.action_of_gens(M)))
    from(M) = Amodule(backtransform_matrix.(Hecke.action_of_gens(M)))
    return to, from
end

right_conjugate(a, t) = inv(t) * a * t
left_conjugate(a, t) = t * a * inv(t)

submatrix(A::fmpq_mat, n::Int) = (@assert A[1:n, n+1:end] == 0; A[1:n, 1:n])


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
