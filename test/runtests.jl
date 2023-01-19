using RationalMeatAxe
using Hecke
using Test

# Hecke.meataxe over fields of characteristic zero will fail in general.
# Below are some tests, that certify this and tests showing RationalMeatAxe accomplishes this.
#
# For completeness of tests, these are MeatAxe.jl’s exports:
# submodules, minimal_submodules, maximal_submodules, composition_series, composition_factors_with_multiplicity, meataxe
#
# Eventually, we also want tests over other fields than ℚ.
# The algorithmic components of the new algorithm shall also be unit tested.

@testset "RationalMeatAxe.jl" begin

    # example by Claus Fieker, using Oscar
    # generators = mat.(irreducible_modules(QQ, transitive_group(8, 5))[end].ac)
    generators1 = MatrixSpace(QQ,4,4).([
        [ 0  1  0  0
         -1  0  0  0
          0  0  0 -1
          0  0  1  0],
        [ 0  0 -1  0
          0  0  0 -1
          1  0  0  0
          0  1  0  0]
     ])
    generators2 = MatrixSpace(QQ,3,3).([[0 1 0;1 0 0;0 0 1], [0 1 0;0 0 1;1 0 0]])

    M1 = Hecke.Amodule(generators1)
    M2 = Hecke.Amodule(generators2)

    M2sub1gens = MatrixSpace(QQ,1,1).([[1],[1]])
    M2subHecke = Hecke.composition_factors(M2)
    M2sub = RationalMeatAxe.meataxe(M2)

    @testset "Hecke fails" begin
        @test_throws "Too many attempts" Hecke.meataxe(M1)
        @test Hecke.composition_factors(M1) skip=true
        @test Hecke.composition_factors_with_multiplicity(M1) skip=true
        @test Hecke.composition_series(M1) skip=true

        @test M2sub1gens in Hecke.action_of_gens.(M2subHecke)
        @test sort(dim.(M2subHecke)) == [1,2]
    end

    @testset "meataxe" begin
        @test RationalMeatAxe.meataxe(M1) == [M1]
        @test M2sub1gens in Hecke.action_of_gens.(M2sub)
        @test sort(dim.(M2sub)) == [1,2]
    end

end
