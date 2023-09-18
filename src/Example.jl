"""
    meataxe(gens::Vector{<:MatElem}) :: Vector{<:MatElem}

Return basis for which `gens` is in block diagonal form, by giving bases for the blocks
"""
function meataxe(gens::Vector{<:MatElem})
    M = Hecke.Amodule(gens)
    Msub = meataxe(ThisModule(M))
    basismats = totalmat.(Msub)
    return basismats
end

function example_data(gens::Vector{<:MatElem})
    bases = meataxe(gens)
    basis = reduce(vcat, bases)
    invbasis = inv(basis)
    newgens = [basis] .* gens .* [invbasis]
    blocks = nrows.(bases)
    return (; bases, invbasis, gens, newgens, blocks)
end
function example_as_latex(gens::Vector{<:MatElem})
    (; bases, invbasis, gens, newgens, blocks) = example_data(gens)
    join(stdout, ("a_{$i} =\n" * latex_matrix(g) for (i,g) in enumerate(gens)), "\\quad\n")
    println("\\\\\nt =\n", divided_latex_matrix(bases), "\\quad")
    println("t^{-1} =\n", col_divided_latex_matrix(invbasis, blocks), "\\\\")
    join(stdout, ("a'_{$i} = t a_{$i} t^{-1} =\n" * latex_block_matrix(g, blocks) for (i,g) in enumerate(newgens)), "\\quad\n")
    nothing
end

latex_matrix(m::MatElem) = "\\begin{pmatrix}\n" * latex_matrix_content(m) * "\n\\end{pmatrix}\n"

latex_matrix_content(m::MatElem) = latex_matrix_content([sprint(show, MIME("text/latex"), x) for x in m])
function latex_matrix_content(m::Matrix{String})
    rows = (join(row, " & ") for row in eachrow(m))
    join(rows, " \\\\\n")
end

function divided_latex_matrix(ms::Vector{<:MatElem})
    contents = latex_matrix_content.(ms)
    content = join(contents, " \\\\\n\\hline\n")
    """
    \\begin{pmatrix}
    $content
    \\end{pmatrix}
    """
end

function col_divided_latex_matrix(m::MatElem, lengths::Vector{Int})
    @assert sum(lengths) == ncols(m)
    colspec = join('c'.^lengths, '|')
    """
    \\begin{array}{$colspec}
    $(latex_matrix_content(m))
    \\end{array}
    """
end

function latex_block_matrix(m::MatElem, blocks::Vector{Int})
    @assert sum(blocks) == ncols(m) == nrows(m)
    intervals = intervals_from_lengths(blocks)
    for I in intervals, J in intervals; I===J || @assert m[I,J] == 0 end
    s = fill("", size(m))
    for I in intervals
        s[I,I] = [sprint(show, MIME("text/latex"), x) for x in m[I,I]]
    end
    """
    \\begin{pmatrix}
    $(latex_matrix_content(s))
    \\end{pmatrix}
    """
end

function intervals_from_lengths(v::Vector{Int})
    ends = cumsum(v)
    starts = [1; ends[begin:end-1].+1]
    [s:e for (s,e) in zip(starts,ends)]
end
