raw"""
    AbstractSubModule{S,T,U}

A submodule together with a projection onto it.

For `a::AbstractSubModule` …
`domain(a)::AbstractSubModule` gives the supermodule,
`ancestor(a)::ModAlgAss` gives the super$^\infty$-module,
`codomain(a)::ModAlgAss` gives the submodule,
`mat(a)::MatrixElem` gives the projection from `domain(a)` onto `codomain(a)`,
`image(a, x)` maps algebra actions from `domain(a)` to `codomain(a)`,
`projection(a)::MatrixElem` gives the projection from `ancestor(a)` onto `codomain(a)`,
`invmat(a)` and `invprojection(a)` give the inverse matrices.
"""
abstract type AbstractSubModule{S,T,U} end

struct ThisModule{S,T,U} <: AbstractSubModule{S,T,U}
    M :: Hecke.ModAlgAss{S,T,U}
end
domain(a::ThisModule) = a
ancestor(a::ThisModule) = a.M
codomain(a::ThisModule) = a.M
image(a::ThisModule, x) = x
mat(a::ThisModule) = identity_matrix(coefficient_ring(a.M), dim(a.M))
invmat(a::ThisModule) = mat(a)
projection(a::ThisModule) = mat(a)
invprojection(a::ThisModule) = mat(a)

raw"""
    SubModule{S}(M::Hecke.ModAlgAss{<:Any, S}, A::S) where S<:MatrixElem

Module automorphism from $M$ to $M⋅T$, where $AT=H$ is the HNF of an endomorphism $A$.
The image thus has dimension `rank(H)`. Intended for use with a projection $A$.
"""
@attributes mutable struct SubModule{S,Q,U} <: AbstractSubModule{S,Q,U}
    rank :: Int
    T :: Q
    invT :: Q
    ancestor :: Hecke.ModAlgAss{S,Q,U}
    domain :: AbstractSubModule{S,Q,U}
    # Sei 𝓐 ⊆ K^{𝑚×𝑚} K-rechts-Algebra, jedes X∈𝓐 also auf dem Modul $M=K^𝑚$
    # von rechts operierende Matrix.
    # Ferner sei A∈End_K(𝓐), also AX=XA und H=AT die Spalten-HNF von A mit 𝑛 nicht-null-Spalten.
    # Vermittels des Isomorphismus M⋅A → M⋅H=M⋅AT, m ↦ mT operiert X auf m∈M⋅H als mT⁻¹XT.
    # Nun hat HT⁻¹XT = AXT = XAT = XH ebenfalls nur n nicht-null-Spalten, ist also von der Form
    # (m×n)   0.
    function SubModule(domain::AbstractSubModule{S,Q,U}, A::Q) where {S,Q<:MatrixElem,U}
        H, T = hnf_with_transform(transpose(A))
        T = transpose!(T)
        return new{S,Q,U}(Hecke.rank_of_ref(H), T, inv(T), ancestor(domain), domain)
    end
end
SubModule(a::Hecke.ModAlgAss{S,T,U}, A::T) where {S,T,U} = SubModule(ThisModule(a), A)
SubModule(a::Hecke.ModAlgHom) = SubModule(domain(a), matrix(a))

domain(a::SubModule) = a.domain
ancestor(a::SubModule) = a.ancestor
mat(a::SubModule) = a.T
invmat(a::SubModule) = a.invT

@attr Hecke.ModAlgAss{S,T,U} codomain(a::SubModule{S,T,U}) where {S,T,U} = image(a, domain(a))

image(h::SubModule{S,T,U}, x::T) where {S,T,U} = submatrix(h.invT * x * h.T, h.rank)::T
image(h::SubModule{S,T,U}, M::Hecke.ModAlgAss{S,T,U}) where {S,T,U} = Amodule(image.((h,), Hecke.action(M)))::Hecke.ModAlgAss{S,T,U}
image(h::SubModule{S,T,U}, M::AbstractSubModule{S,T,U}) where {S,T,U} = image(h, codomain(M))::Hecke.ModAlgAss{S,T,U}

submatrix(A::QQMatrix, n::Int) = (@req A[1:n, n+1:end] == 0 "The lower matrix entries must be zero. Possibly you created a `SubModule` with a non-endomorphism."; A[1:n, 1:n])

"""
    projection(a::AbstractSubModule)

For `M=ancestor(a)` and `N=codomain(a)` return `T` with `M⋅T=N`.
"""
projection(::AbstractSubModule)

@attr projection(a::SubModule) = _projection(domain(a), mat(a))
_projection(::ThisModule, T) = T
function _projection(a::SubModule, Tn)
    # N = M⋅T0⋅T1⋅⋅⋅Tn = M⋅T⋅Tn = project(M⋅T)⋅Tn
    T = deepcopy(projection(a))
    Tsub = @view(T[:, 1:ncols(Tn)])
    Tsub = mul!(Tsub, Tsub, Tn)
    return T
end

@attr invprojection(a::SubModule) = _invprojection(domain(a), invmat(a))
_invprojection(::ThisModule, T) = T
function _invprojection(a::SubModule, Tn)
    T = deepcopy(invprojection(a))
    Tsub = @view(T[1:ncols(Tn), :])
    Tsub = mul!(Tsub, Tn, Tsub)
    return T
end
