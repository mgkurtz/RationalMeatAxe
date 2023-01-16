module RationalMeatAxe

using Hecke
using Markdown

using Hecke: ModAlgHom, AlgElem

Mod = Hecke.ModAlgAss

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
    B = elements(lll(saturate(matrix(basis(z)))))
    for b in B
        f = minpoly(b)
        is_irreducible(f) && deg(f) == 1 && return [M]
        fs = factor(f)
        length(fs) == 1 && continue
        f1 = p^e
        f2 = divexact(f, f1)
        b1 = zhom(f1(b))
        b2 = zhom(f2(b))
        ss1 = homogeneous_components(b1)
        ss2 = homogeneous_components(b2)
        return [ss1; ss2]
    end
    return [M]
end

function homogeneous_components(f::ModAlgHom) :: Vector{Mod}
    s, embed = image(f)
    embed.(homogeneous_components(s))
end

function center_of_endomorphism_ring(M::Mod)
    endM, endMhom = endomorphism_algebra(M)
    z, zhom = center(endM)
    return z, zhom * endMhom
end


# Stolen from `ideal_from_lattice_gens` in AlgAssAbsOrd/Ideal.jl
function matrix(v::Vector{AlgAssElem{fmpq}}) :: fmpz_mat
    @assert !isempty(v)
    M = zero_matrix(ZZ, length(v), dim(parent(v[1])))
    _spam = ZZ(0)
    for (i, a) in enumerate(v)
        elem_to_mat_row!(M, i, _spam, a)
    end
    M
end

function elements(a::AlgAss{fmpq}, m::Union{fmpz_mat, fmpq_mat})
    v = Vector{AlgAssElem{fmpq, AlgAss{fmpq}}}(undef, size(m, 1))
    for i in axes(m, 1)
        v[i] = elem_from_mat_row(a, m, i)
    end
    v
end

function image(f::ModAlgHom) :: Tuple{Mod, Function}
    A = matrix(f)
    m = size(A, 1)
    @assert m == size(A, 2)
    H, T = hnf_with_transform(A) # TA=H
    n = rank(T)
    @assert n < m
    to, from = sub_morphisms(T, n, m)
    M = codomain(f)
    return to(M), from
end

# Zeilen von `A` bzw. `H` sollen Submodul `N` von `M` erzeugen.
# mHx = mTAx = mTxA = mTxT⁻¹TA =mTxT⁻¹H
# Ist `M` durch Menge `X` von Matrizen erzeugt, so ist `N` durch
# { TxT⁻¹ : x∈X } erzeugt.
function sub_morphisms(T::fmpz_mat, n::Int)
    transform_matrix(x) = submatrix(conjugate(x, T), n)
    backtransform_matrix(x) = conjugate(embedmatrix(x, m), inv(T))
    to(M) = Amodule(transform_matrix.(action_of_gens(M)))
    from(M) = Amodule(backtransform_matrix.(action_of_gens(M)))
    return to, from
end

conjugate(a, t) = inv(t) * a * t

function submatrix(A::fmpz_mat, n::Int)
    @assert A[:, n+1:end] == 0
    @assert A[n+1:end, :] == 0
    A[1:n, 1:n]
end

function embedmatrix(A::fmpz_mat, n::Int)
    B = zero(MatrixSpace(ZZ, n, n))
    B[1:n, 1:n] = A
end

# ===

@doc Markdown.doc"""
    split_homogeneous(M::Mod) -> Vector{Mod}

Return pairwise isomorphic simple $S_i$ such that $M=\bigoplus_i S_i=M$.

The input $M$ needs to be homogeneous, i.e. allow such a decomposition.

See also [`homogeneous_components(::Mod)`](@ref).
"""
function split_homogeneous(M::Mod)
    endM, endMhom = endomorphism_algebra(M)
    o = maximal_order(endM)
    # TODO m,s
    true && return [M]
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

is_split(a::Element) = !is_irreducible(minpoly(a))

end
