# Note uses the abstract type `Operator` from diff.jl

"""
$(TYPEDEF)

Represents an integral operator.

# Fields
$(FIELDS)

# Examples

```jldoctest
julia> using Symbolics

julia> @variables x y;

julia> Ix = Integral(x) # Indefinite integral
Integral(x)

julia> Ix(y) # Integrate y wrt. x
Integral(x)(y)

julia> Ixy = Integral(x) * Integral(y) # ∫ dx dy operator
Integral(x) ∘ Integral(y)

julia> Ixab = Integral(x, 1, 2) # Definite integral wrt x between 1 and 2
Integral(x, 1 .. 2)
```
"""
abstract type Integral <: Operator end

struct IndefiniteIntegral <: Integral
    """The variable to integrate with respect to."""
    x
    IndefiniteIntegral(x) = new(value(x))
    IndefiniteIntegral(x::Union{AbstractFloat, Integer}) = error("I(::Number) is not a valid integral. Integrals must be taken w.r.t. symbolic variables.")
end

struct DefiniteIntegral{T <: Symbolics.VarDomainPairing} <: Integral
    """The variable to integrate with respect to."""
    x
    domain::T
    DefiniteIntegral(x, domain) = new{typeof(domain)}(value(x), domain)
    IndefiniteIntegral(x::Union{AbstractFloat, Integer}, domain) = error("I(::Number) is not a valid integral. Integrals must be taken w.r.t. symbolic variables.")
end

Integral(x) = IndefiniteIntegral(x)
Integral(d::Symbolics.VarDomainPairing) = DefiniteIntegral(d.variables, d)
Integral(x, a::Union{Rational, AbstractIrrational, AbstractFloat, Integer}, b::Union{Rational, AbstractIrrational, AbstractFloat, Integer}) = DefiniteIntegral(x, VarDomainPairing(x, DomainSets.ClosedInterval(a, b)))

function (I::Integral)(x)
    x = unwrap(x)
    if isarraysymbolic(x)
        array_term(I, x)
    else
        term(I, x)
    end
end

(I::Integral)(x::Union{Num, Arr}) = wrap(I(unwrap(x)))
(I::Integral)(x::Complex) = wrap(ComplexTerm{Real}(I(unwrap(real(x))), I(unwrap(imag(x)))))
SymbolicUtils.promote_symtype(::IndefiniteIntegral, T) = T
SymbolicUtils.promote_symtype(::DefiniteIntegral, x) = x
SymbolicUtils.isbinop(f::IndefiniteIntegral) = false
SymbolicUtils.isbinop(f::DefiniteIntegral) = false

is_integral(x) = iscall(x) ? operation(x) isa Integral : false

Base.:*(I1, I2::Integral) = I1 ∘ I2
Base.:*(I1::Integral, I2) = I1 ∘ I2
Base.:*(I1::Integral, I2::Integral) = I1 ∘ I2
Base.:^(I::Integral, n::Integer) = iszero(n) ? identity : _repeat_apply(I, n)

Base.show(io::IO, I::IndefiniteIntegral) = print(io, "Integral(", I.x, ")")
function Base.show(io::IO, I::DefiniteIntegral)
    print(io, "Integral(", I.domain.variables, ", ", I.domain.domain, ")")
end

Base.nameof(I::IndefiniteIntegral) = :IndefiniteIntegral
Base.nameof(I::DefiniteIntegral) = :DefiniteIntegral

Base.:(==)(I1::IndefiniteIntegral, I2::IndefiniteIntegral) = isequal(I1.x, I2.x)
Base.:(==)(I1::DefiniteIntegral, I2::DefiniteIntegral) = isequal(I1.x, I2.x) && convert(Bool, simplify(isequal(I1.domain, I2.domain)))

Base.hash(I::IndefiniteIntegral, u::UInt) = hash(I.x, xor(u, 0x2b27231e0d63f5a3))
Base.hash(I::DefiniteIntegral, u::UInt) = hash(I.x, xor(u, 0x5cf367b76a62541a))

function (I::DefiniteIntegral)(x::Union{Rational, AbstractIrrational, AbstractFloat, Integer})
    domain = I.domain.domain
    a, b = value.(DomainSets.endpoints(domain))
    wrap((b - a)*x)
end
(I::DefiniteIntegral)(x::Num) = Num(I(Symbolics.value(x)))

"""
    hasintegral(O)

Returns true if the expression or equation `O` contains [`Integral`](@ref) terms.
"""
hasintegral(O) = recursive_hasoperator(Integral, O)

"""
    executeintegral(I, arg, simplify=false; throw_no_integral=false)

Apply the passed Integral I on the passed argument.

This function differs to `expand_integrals` in that in only expands the
passed integral and not any other Integrals it encounters.

# Arguments
- `I::Integral`: The integral to apply
- `arg::Symbolic`: The symbolic expression to apply the differential on.
- `simplify::Bool=false`: Whether to simplify the resulting expression using
    [`SymbolicUtils.simplify`](@ref).
- `throw_no_integral=false`: Whether to throw if a function with unknown
    integral is encountered.
"""
function executeintegral(I, arg, simplify=false; throw_no_integral=false)
    occursin_info(I.x, arg) || return arg * I(1)

    if !iscall(arg)
        return I(arg) # Cannot expand
    elseif (op = operation(arg); issym(op))
        return I(arg) # Cannot expand
    elseif op === getindex
        return I(arg)
    elseif op === ifelse
        args = arguments(arg)
        O = op(args[1],
            executeintegral(I, args[2], simplify; throw_no_integral),
            executeintegral(I, args[3], simplify; throw_no_integral))
        return O
    elseif isa(op, Integral)
        return I(arg) # Cannot expand
    elseif isa(op, Differential) && isa(I, DefiniteIntegral) && isequal(op.x, I.x)
        inner = arguments(arg)[1]
        domain = I.domain.domain
        a, b = value.(DomainSets.endpoints(domain))
        return substitute(inner, Dict(I.x => b)) - substitute(inner, Dict(I.x => a))
    elseif isa(op, Differential) && isa(I, IndefiniteIntegral) && isequal(op.x, I.x)
        return I(arg) # Cannot expand
    elseif isa(op, Differential) && !isequal(op.x, I.x)
        # Derivative and integral commute
        inner = arguments(arg)[1]
        return op(executeintegral(I, inner))
    elseif op === +
        # Integral of sum is equal to sum of integrals
        inner_args = arguments(arg)
        return sum(inner_args, init=0) do a
            return executeintegral(I, a; throw_no_integral)
        end
    elseif op === *
        # Any factors that do not depend on I.x can be moved out of the integral.
        inner_args = arguments(arg)
        l = length(inner_args)
        prefactor = 1
        integrand = 1

        for i in 1:l
            if occursin_info(I.x, inner_args[i])
                integrand *= inner_args[i]
            else
                prefactor *= inner_args[i]
            end
        end

        if isequal(prefactor, 1)
            if simplify
                return I(simplify(arg))
            else
                return I(arg)
            end
        end

        if simplify
            return Symbolics.simplify(prefactor) * executeintegral(I, Symbolics.simplify(integrand))
        else
            return prefactor * executeintegral(I, integrand)
        end
    elseif op === /
        # Any factors that do not depend on I.x can be moved out of the integral.
        inner_args = arguments(arg)

        occursin_numerator = occursin_info(I.x, inner_args[1])
        occursin_denominator = occursin_info(I.x, inner_args[2])

        if simplify
            args = simplify(args)
            numerator = simplify(inner_args[1])
            denominator = simplify(inner_args[2])
        else
            numerator = inner_args[1]
            denominator = inner_args[2]
        end

        if occursin_numerator && occursin_denominator
            return I(args)
        elseif occursin_numerator
            return 1/denominator * executeintegral(I, numerator)
        elseif occursin_denominator
            # Could also try to pull out any factors in denominator that do not depend on
            # I.x?
            return numerator * I(1/denominator)
        else
            return args * I(1)
        end
    else
        error("`executeintegral()` does not know how to handle operator $op with integral $I")
    end
end

"""
$(SIGNATURES)

Expands integrals within a symbolic expression `O`.

This function recursively traverses a symbolic expression, applying any known integral
rules to expand any integrals it encounters.

# Arguments
- `O::Symbolic`: The symbolic expression to expand.
- `simplify::Bool=false`: Whether to simplify the resulting expression using
    [`SymbolicUtils.simplify`](@ref).

# Keyword Arguments
- `throw_no_integral=false`: Whether to throw if a function with unknown
   integral is encountered.

# Examples
```jldoctest
julia> @variables x y z k;

julia> f = k*(abs(x-y)/y-z)^2
k*((-z + abs(x - y) / y)^2)

julia> Ix = Integral(x) # Indefinite integral wrt x
Integral(x)

julia> ifx = expand_integrals(Ix(f))
k*Integral(x)((-z + abs(x - y) / y)^2)
```
"""
function expand_integrals(O::Symbolic, simplify=false; throw_no_integral=false)
    if iscall(O) && isa(operation(O), Integral)
        arg = only(arguments(O))
        arg = expand_integrals(arg, false; throw_no_integral)
        return executeintegral(operation(O), arg, simplify; throw_no_integral)
    elseif !hasintegral(O)
        return O
    else
        args = map(a->expand_integrals(a, false; throw_no_integral), arguments(O))
        O1 = operation(O)(args...)
        return simplify ? SymbolicUtils.simplify(O1) : O1
    end
end
function expand_integrals(n::Num, simplify=false; kwargs...)
    wrap(expand_integrals(value(n), simplify; kwargs...))
end
expand_integrals(x, simplify=false; kwargs...) = x

# Indicate that no integral is defined.
struct NoIntegral
end

"""
    Symbolics.integral(::typeof(f), args::NTuple{N, Any}, ::Val{i})

Return the integral of `f(args...)` with respect to `args[i]`. `N` should be the number
of arguments that `f` takes and `i` is the argument with respect to which the derivative
is taken. The result can be a numeric value (if the integral is constant) or a symbolic
expression. This function is useful for defining derivatives of custom functions registered
via `@register_symbolic`, to be used when calling `expand_integrals`.
"""
integral(f, args, v) = NoIntegral()

integral(f::Function, x::Num) = integral(f(x), x)
integral(::Function, x::Any) = TypeError(:integral, "2nd argument", Num, typeof(x)) |> throw

_repeat_apply(f::Integral, n) = n == 1 ? f : ComposedFunction{Any,Any}(f, _repeat_apply(f, n-1))

"""
$(SIGNATURES)

A helper function for computing the integral of the expression `O` with respect to `var`.

# Keyword Arguments

- `simplify=false`: The simplify argument of `expand_integrals`.

All other keyword arguments are forwarded to `expand_integrals`.
"""
function integral(O, var; simplify=false, kwargs...)
    if O isa AbstractArray
        Num[Num(expand_integrals(Integral(var)(value(o)), simplify; kwargs...)) for o in O]
    else
        Num(expand_integrals(Integral(var)(value(O)), simplify; kwargs...))
    end
end

function SymbolicUtils.substitute(op::Integral, dict; kwargs...)
    @set! op.x = substitute(op.x, dict; kwargs...)
end
