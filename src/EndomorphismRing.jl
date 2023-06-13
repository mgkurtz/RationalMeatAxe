function modularized_center_of_endomorphism_ring(M::Mod)
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
