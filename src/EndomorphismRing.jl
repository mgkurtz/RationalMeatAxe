function modularized_center_of_endomorphism_ring(M::Hecke.ModAlgAss)
    @req characteristic(base_ring(M)) == 0
    m = rand_prime()
    M_mod_m = M % m
    c_mod_m, from_c_mod_m = center_of_endomorphism_ring(M_mod_m)
    done, c = rational_reconstruction(p, c_mod_m)
    while !done
        p = rand_prime()
        M_mod_p = M % p
        c_mod_p, from_c_mod_p = center_of_endomorphism_ring(M_mod_p)
        c_mod_m = crt(c_mod_m, c_mod_p, m, p)
        m *= p
        done, c = rational_reconstruction(p, c_mod_m)
    end

end

function center_of_endomorphism_ring(M::Hecke.ModAlgAss{<:FinField})
    # p = characteristic(base_ring(M))
    cs = Hecke.composition_series(ThisModule(M))
    to_reference_basis.(cs)
    # TODO Baue Subquotienten S_i
    # TODO Bestimme Hom_A(S_i, S_j)
    # TODO Baue daraus Hom_A(M, M)
    # cs[i] ⊆ cs[j] for i≤j
    # cs[i] generates submodule, ie. ∀ m ∈ action(M): cs[i] * m == x * cs[i]
    # ∄ cs[i] ⊊ a ⊊ cs[i+1]: a generates submodule
    # s[i] ≔ cs[i] / cs[i-1]
    # Wie erkennen wir, ob S≅T? Vielleicht, ob obige Menge funktioniert? → erstmal `is_isomorphic` nutzen.
    # Wie bauen wir die Hom_A(S,T) zusammen? → siehe Notizen
end

SubQuoModule(domain::Hecke.ModAlgAss{S,T,U}, sub::T, quo::T)

function center_of_hom_space_for_irreducible(M::SubQuoModule{S,T,U}, N::SubQuoModule{S,T,U}) :: T
    @req is_irreducible(M)
    @req base_ring(M) == base_ring(N)
    is_isomorphic(M, N) || return zero_matrix(base_ring(M), dim(M)*dim(N), 0)
    # Wie sieht Hom_A(S,T) für S≅T aus? → fixiere s∈S; Schiefkörper {φₘ : m∈T} mit φₘ(sa)=ma.
    # 

end

raw"""
    word_basis(M) :: Vector{Vector{Int}}

Basis of $M$ expressed as words in the algebra.
The first entry is the empty word.

We have word_basis(M) == word_basis(N) iff M and N are isomorphic.
"""
# TODO: See Hecke._relations
function word_basis(M::SubQuoModule)
end

is_isomorphic(M::SubQuoModule, N::SubQuoModule) = word_basis(M) == word_basis(N)

raw"""
    to_reference_basis(M::SubQuoModule) -> SubQuoModule

Change basis such that `basis(N)` is `basis(N)[1:1] .* word_basis(M)`.
"""
function to_reference_basis(M::SubQuoModule)
end

struct SimpleComponent{T}
    word_basis :: Vector{Vector{Int}}
    relations :: Vector{Vector{Int}} #?
    endomorphisms :: Vector{T}
    function SimpleComponent(A, word_basis)
        # endo[i] in erster Zeile e_i,
        # e_2 == e_1*word ↦ e_i*word
        #
    end
end

function endomorphisms()
end

raw"""
    _homomorphism(M::ModAlgAss{S,T,U}, N::ModAlgAss{S,T,U}, p::Int) -> T

The homomorphism mapping the first basis vector of $M$ to the $p$-th basis vector of $N$ with respect to the `word_basis`.
"""
function _endomorphism(M, k::Int)
    @req is_in_word_basis(M); @req is_in_word_basis(N)
end
