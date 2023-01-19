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

    #=
    @testset "transitive_group(8,5) on QQ^4" begin
        # example by Claus Fieker, using Oscar
        # generators = mat.(irreducible_modules(QQ, transitive_group(8, 5))[end].ac)
        generators = MatrixSpace(QQ,4,4).([
            [ 0  1  0  0
             -1  0  0  0
              0  0  0 -1
              0  0  1  0],
            [ 0  0 -1  0
              0  0  0 -1
              1  0  0  0
              0  1  0  0]
         ])
        M = Hecke.Amodule(generators)

        @testset "Hecke fails" begin
            @test_throws "Too many attempts" Hecke.meataxe(M)
            @test Hecke.composition_factors(M) skip=true
            @test Hecke.composition_factors_with_multiplicity(M) skip=true
            @test Hecke.composition_series(M) skip=true
        end
        @testset "Rational Meataxe" begin
            @test RationalMeatAxe.meataxe(M) == [M]
        end
    end
    =#


    @testset "Sym(3) on QQ^3" begin
        generators = MatrixSpace(QQ,3,3).([[0 1 0;1 0 0;0 0 1], [0 1 0;0 0 1;1 0 0]])
        M = Hecke.Amodule(generators)
        Msub1gens = MatrixSpace(QQ,1,1).([[1],[1]])

        @testset "Hecke" begin
            MsubHecke = Hecke.composition_factors(M)
            @test Msub1gens in Hecke.action_of_gens.(MsubHecke)
            @test sort(dim.(MsubHecke)) == [1,2]
        end

        @testset "Rational Meataxe" begin
            Mhomogenous = RationalMeatAxe.homogeneous_components(M)
            @test length(Mhomogenous) == 2
            # Msub = RationalMeatAxe.meataxe(M)
            @test RationalMeatAxe.meataxe(M1) == [M1]
            @test M2sub1gens in Hecke.action_of_gens.(M2sub)
            @test sort(dim.(M2sub)) == [1,2]
        end
    end

end
