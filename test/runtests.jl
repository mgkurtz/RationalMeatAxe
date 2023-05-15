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

Hecke.set_verbosity_level(:rma, 1)

# example by Claus Fieker, using Oscar
# generators = mat.(irreducible_modules(QQ, transitive_group(8, 5))[end].ac)
gens1 = MatrixSpace(QQ,4,4).([
    [ 0  1  0  0
     -1  0  0  0
      0  0  0 -1
      0  0  1  0],
    [ 0  0 -1  0
      0  0  0 -1
      1  0  0  0
      0  1  0  0]
 ])
M1 = Hecke.Amodule(gens1)

gens2 = MatrixSpace(QQ,3,3).([[0 1 0;1 0 0;0 0 1], [0 1 0;0 0 1;1 0 0]])
M2 = Hecke.Amodule(gens2)
M2sub1gens = MatrixSpace(QQ,1,1).([[1],[1]])

using RationalMeatAxe.RandomAlgebras

Mrands = [RandomAlgebras.rand_sum_of_matrix_algebras(make(QQ, -i:i), i, i, i) for i in 2:4]

if false
@testset "Hecke.jl" begin
    @testset "transitive_group(8,5) on QQ^4" begin
        @test_throws "Too many attempts" Hecke.meataxe(M1)
        @test Hecke.composition_factors(M1) skip=true
        @test Hecke.composition_factors_with_multiplicity(M1) skip=true
        @test Hecke.composition_series(M1) skip=true
    end
    @testset "Sym(3) on QQ^3" begin
        MsubHecke = Hecke.composition_factors(M2)
        @test M2sub1gens in Hecke.action_of_gens.(MsubHecke)
        @test sort(dim.(MsubHecke)) == [1,2]
    end
end
end


@testset "RationalMeatAxe.jl" begin
    @testset "center of End: $i" for (i, M) in Iterators.enumerate(Mrands)
        z, zhom = RationalMeatAxe.center_of_endomorphism_ring(M)
        for a in matrix.(zhom.(basis(z))), m in M.action_of_gens
            @test a * m == m * a
        end
    end

    @testset "basis of center of End: $i" for (i, M) in Iterators.enumerate(Mrands[1:1])
        B = RationalMeatAxe.basis_of_center_of_endomorphism_ring(M)
        @test B !== nothing
        for a in B, m in M.action_of_gens
            @test a * m == m * a
        end
    end

    @testset "Sym(3) on QQ^3" begin
        @test RationalMeatAxe.homogeneous_components(M1) == [M1]
    end
    @testset "transitive_group(8,5) on QQ^4" begin
        @testset "homogeneous components" begin
            Mhomogenous = RationalMeatAxe.homogeneous_components(M2)
            @test length(Mhomogenous) == 2
        end
        if false # broken
        @testset "meataxe" begin
            Msub = RationalMeatAxe.meataxe(M2)
            @test Msub == [M2]
            @test M2sub1gens in Hecke.action_of_gens.(Mhomogenous)
            @test sort(dim.(Mhomogenous)) == [1,2]
        end
        end
    end
    @testset "random" begin
    end
end
