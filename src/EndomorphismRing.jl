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
    cs = Hecke.composition_series(M)
    # cs[i] ⊆ cs[j] for i≤j
    # cs[i] generates submodule, ie. ∀ m ∈ action(M): cs[i] * m == x * cs[i]
    # ∄ cs[i] ⊊ a ⊊ cs[i+1]: a generates submodule
    # s[i] ≔ cs[i] / cs[i-1]
    # Wie sieht Hom_A(S,T) für S≅T aus? → fixiere s∈S; Schiefkörper {φₘ : m∈T} mit φₘ(sa)=ma.
    # Wie erkennen wir, ob S≅T? Vielleicht, ob obige Menge funktioniert?
    # Wie bauen wir die Hom_A(S,T) zusammen? → siehe Notizen


end
