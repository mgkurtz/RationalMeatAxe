raw"""
    AbstractSubModule{S,T,U}

A submodule together with a corresponding basis in the supermodule.

For `a::AbstractSubModule` …
`domain(a)::AbstractSubModule` gives the supermodule,
`ancestor(a)::ModAlgAss` gives the super$^\infty$-module,
`codomain(a)::ModAlgAss` gives the submodule,
`mat(a)::MatrixElem` gives the column basis of `codomain(a)` as subset of `domain(a)`,
`image(a, x)` maps algebra actions from `domain(a)` to `codomain(a)`,
`totalmat(a)::MatrixElem` like `mat`, but wrt. `ancestor(a)`,
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
totalmat(a::ThisModule) = mat(a)

raw"""
    SubModule{S}(M::Hecke.ModAlgAss{S,T,U}, A::T) where T<:MatrixElem

Submodule `MA`=$M⋅A$ for a projection $A$.

Let $X$ be an action on $M$ and $R=TA$ a reduced row echolon form of $A$.
Then $M⋅A=M⋅R$ and $RX=TAX=TXA=TXT⁻¹TA=TXT⁻¹R=YR$, where $Y=RX/R$.
By restricting $R$ to its $k$ non-zero rows, $Y$ becomes $k×k$.
So, we represent $M⋅A$ as $M⋅R$ with transformed actions.
"""
@attributes mutable struct SubModule{S,T,U} <: AbstractSubModule{S,T,U}
    R :: T
    ancestor :: Hecke.ModAlgAss{S,T,U}
    domain :: AbstractSubModule{S,T,U}
    function SubModule(domain::AbstractSubModule{S,T,U}, A::T) where {S,T<:MatrixElem,U}
        # @req is_pseudoidempotent(A) "Matrix must be pseudo-idempotent, but $(A*A)!=λ*$A"
        k, R = rref(A)
        return new{S,T,U}(R[1:k,:], ancestor(domain), domain)
    end
end
SubModule(a::Hecke.ModAlgAss{S,T,U}, A::T) where {S,T,U} = SubModule(ThisModule(a), A)
SubModule(M::SubModule, a::Hecke.ModAlgHom) = (@req codomain(M)==domain(a) "Homomorphism domain incorrect"; SubModule(M, matrix(a)))

domain(a::SubModule) = a.domain
ancestor(a::SubModule) = a.ancestor
mat(a::SubModule) = a.R

sub_module_type(S, T) = Hecke.AlgMat{elem_type(S), T}

@attr Hecke.ModAlgAss{S,T,sub_module_type(S,T)} codomain(a::SubModule{S,T}) where {S,T} = image(a, domain(a))

image(h::SubModule{S,T,U}, x::T) where {S,T,U} = solve_left(h.R, h.R * x) :: T
image(h::SubModule{S,T}, M::Hecke.ModAlgAss{S,T}) where {S,T} = Amodule(image.((h,), Hecke.action(M)))::Hecke.ModAlgAss{S,T,sub_module_type(S,T)}
image(h::SubModule{S,T}, M::AbstractSubModule{S,T}) where {S,T} = image(h, codomain(M))::Hecke.ModAlgAss{S,T,sub_module_type(S,T)}

function is_pseudoidempotent(a::MatrixElem)
    # TODO: Does not handle ℚ^{k×k}^{n×n} matrices, where the ℚ^{k×k} part comes from a number field and shall be interpreted like a scalar
    aa = a*a
    aa == 0 && return a == 0
    return find(!is_zero, aa) / find(!is_zero, a) * a == aa
end

"""
    totalmat(a::AbstractSubModule)

For `M=ancestor(a)` and `N=codomain(a)` return `C` with `C⋅M=N`.

`C` is in reduced column echolon form.
"""
totalmat(::AbstractSubModule)

# M_{n-1} ≥ R_n⋅M_n ⇒ M ≥ R_0⋅⋅⋅R_n⋅M_n
@attr totalmat(a::SubModule) = _totalmat(domain(a), mat(a))
_totalmat(a::SubModule, Rn) = Rn * totalmat(a)
_totalmat(::ThisModule, R) = R

is_basis_of_submodule(a::MatrixElem, M::Hecke.ModAlgAss) =
    rank(a) == nrows(a) && generates_submodule(a, M)

generates_submodule(a::MatrixElem, M::Hecke.ModAlgAss) =
    all(can_solve(a, a * x; side=:left) for x in Hecke.action(M))
