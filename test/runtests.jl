using RationalMeatAxe
using RationalMeatAxe.RandomAlgebras: RandomAlgebras,
    rand_sum_of_matrix_algebras, sum_of_matrix_algebras_gens, rand_invertible
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

structures = [[a for j in 1:i for a in 1:j] for i in 1:3]
Mrands = [RandomAlgebras.rand_sum_of_matrix_algebras(QQ, 0:1, s) for s in structures]

if false
@testset "Hecke.jl" begin
    @testset "transitive_group(8,5) on QQ^4" begin
        @test length(Hecke.decompose(Hecke.endomorphism_algebra(M1))) == 1
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

@testset "center of End: $i" for (i, M) in enumerate(Mrands)
    z = RationalMeatAxe.center_of_endomorphism_ring(M)
    for (a, m) in rand(make(Tuple, z, M.action_of_gens), 10)
        @test a * m == m * a
    end
end

@testset "basis of center of End: $i" for (i, M) in enumerate(Mrands)
    B = RationalMeatAxe.basis_of_center_of_endomorphism_ring(M)
    @test B !== nothing
    for a in B, m in M.action_of_gens
        @test a * m == m * a
    end
end

@testset "submodules" begin
    a, b = 3, 4
    entries = -9:9

    gs = sum_of_matrix_algebras_gens(QQ, [a, b])
    S = MatrixSpace(QQ, a+b, a+b)
    T = rand_invertible(make(S, entries))
    A = zero(S)
    A[1:a,1:a] = identity_matrix(QQ, a)
    gs_ = [inv(T)] .* S.(gs) .* [T]
    A_ = inv(T) * S(A) * T

    M = Amodule(gs_)
    Msub = RationalMeatAxe.SubModule(M, A_)
    M2 = codomain(Msub) # implicitly test assertion about A being an endomorphism

    @test dim(M2) == a
end

function test_meataxe(M::Hecke.ModAlgAss, dims::Vector{Int})
    Msub = RationalMeatAxe.meataxe(RationalMeatAxe.ThisModule(M))
    @test sort(dim.(codomain.(Msub))) == sort(dims)
    for S in Msub
        @test RationalMeatAxe.is_basis_of_submodule(RationalMeatAxe.totalmat(S), M)
    end
    return Msub
end


@testset "Sym(3) on QQ^3" begin
    @testset "homogeneous components" begin
        Mhomogenous = RationalMeatAxe.homogeneous_components(M2)
        @test sort(dim.(Mhomogenous)) == [1,2]
        @test M2sub1gens in Hecke.action_of_gens.(Mhomogenous)
    end
    @testset "meataxe" begin
        Msub = test_meataxe(M2, [1,2])
        @test M2sub1gens in Hecke.action_of_gens.(codomain.(Msub))
    end
end

@testset "random meataxe input $i" for (i, (s, M)) in enumerate(zip(structures, Mrands))
    test_meataxe(M, s)
end

@testset "transitive_group(8,5) on QQ^4" begin
    @test RationalMeatAxe.homogeneous_components(M1) == [M1]
    @test RationalMeatAxe.meataxe(M1) == [M1]
end

@testset "Galois Module" begin
    K, z_7 = cyclotomic_field(7)
    KM, hKM = galois_module(K)
    MKM = Hecke.regular_module(KM)
    test_meataxe(MKM, [1,1,2,2])
    test_meataxe(MKM+MKM, repeat([1,1,2,2], 2))
    test_meataxe(MKM+MKM+MKM, repeat([1,1,2,2], 3))
end

stuff(gens::Vector) = stuff(Hecke.Amodule(gens))
stuff(M::Hecke.ModAlgAss) = ((endM, to_actual_endM) = Hecke.endomorphism_algebra(M); (AA, to_endM) = AlgAss(endM); (A, toAA) = Hecke._as_algebra_over_center(AA); (; M, endM, AA, A, to_actual_endM, to_endM, toAA))
more_stuff(gens::Vector) = more_stuff(Hecke.Amodule(gens))
more_stuff(M::Hecke.ModAlgAss) = ((endM, to_actual_endM) = Hecke.endomorphism_algebra(M); (AA, to_endM) = AlgAss(endM); (A, toAA) = Hecke._as_algebra_over_center(AA); AO = maximal_order(A); endMO = maximal_order(endM); (; M, endM, AA, A, AO, endMO, to_actual_endM, to_endM, toAA))
