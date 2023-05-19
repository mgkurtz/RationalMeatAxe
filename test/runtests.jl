using RationalMeatAxe
using RationalMeatAxe.RandomAlgebras: RandomAlgebras,
    rand_sum_of_matrix_algebras, rand_sum_of_matrix_algebras_gens, rand_invertible
using RandomExtensions
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

Hecke.set_verbosity_level(:rma, 0)

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
        z = RationalMeatAxe.center_of_endomorphism_ring(M)
        for a in z, m in M.action_of_gens
            @test a * m == m * a
        end
    end

    @testset "basis of center of End: $i" for (i, M) in Iterators.enumerate(Mrands)
        B = RationalMeatAxe.basis_of_center_of_endomorphism_ring(M)
        @test B !== nothing
        for a in B, m in M.action_of_gens
            @test a * m == m * a
        end
    end

    @testset "submodules" begin
        a, b = 3, 4
        entries = -9:9

        gs = rand_sum_of_matrix_algebras_gens(make(ZZ, entries), [a => 2, b => 2])
        S = MatrixSpace(QQ, a+b, a+b)
        T = rand_invertible(make(S, entries))
        A = zero(S)
        A[1:a,1:a] = identity_matrix(QQ, a)
        gs_ = [inv(T)] .* S.(gs) .* [T]
        A_ = inv(T) * S(A) * T

        M = Amodule(gs_)
        M2 = RationalMeatAxe.sub(M, A_) # implicitly test some assertions

        @test dim(M2) == a
    end

    @testset "transitive_group(8,5) on QQ^4" begin
        @test RationalMeatAxe.homogeneous_components(M1) == [M1]
        @test RationalMeatAxe.meataxe(M1) == [M1]
    end
    @testset "Sym(3) on QQ^3" begin
        @testset "homogeneous components" begin
            Mhomogenous = RationalMeatAxe.homogeneous_components(M2)
            @test length(Mhomogenous) == 2
            @test M2sub1gens in Hecke.action_of_gens.(Mhomogenous)
            @test sort(dim.(Mhomogenous)) == [1,2]
        end
        @testset "meataxe" begin
            Msub = RationalMeatAxe.meataxe(M2)
            @test length(Msub) == 2
            @test M2sub1gens in Hecke.action_of_gens.(Msub)
            @test sort(dim.(Msub)) == [1,2]
        end
    end
    @testset "rand_sum_of_matrix_algebras_gens" begin
        gs = rand_sum_of_matrix_algebras_gens(make(ZZ, -9:9), [1 => 1, 2 => 2, 3 => 3])
        gs[1][1,1] = 0; @test all(gs[1] .== 0)
        for g in gs[2:3] g[2:3,2:3] .= 0; @test all(g .== 0) end
        for g in gs[4:6] g[4:6,4:6] .= 0; @test all(g .== 0) end
    end
    @testset "random meataxe input $i" for (i, M) in Iterators.enumerate(Mrands)
        Mhomogenous = RationalMeatAxe.homogeneous_components(M)
        Msub = RationalMeatAxe.meataxe(M)
    end
end
