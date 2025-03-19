package it.unive.lisa.tutorial;

import com.ibm.icu.impl.Pair;
import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.*;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonEq;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonNe;
import it.unive.lisa.symbolic.value.operator.unary.LogicalNegation;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.function.Predicate;

public class EqualityDomain implements ValueDomain<EqualityDomain> {
    public static final EqualityDomain BOTTOM = new EqualityDomain();
    public static final EqualityDomain TOP = new EqualityDomain();
    private final HashSet<HashSet<Identifier>> equalities = new HashSet<>();

    private void addEquality(Identifier a, Identifier b) {
        HashSet<Identifier> equalityA = equalities.stream().filter(e -> e.contains(a)).findAny().orElse(null);
        HashSet<Identifier> equalityB = equalities.stream().filter(e -> e.contains(b)).findAny().orElse(null);
        if (equalityA != null) {
            if (equalityB != null) {
                equalityA.addAll(equalityB);
                equalities.remove(equalityB);
                return;
            }
            equalityA.add(b);
            return;
        }
        if (equalityB != null) {
            equalityB.add(a);
            return;
        }
        HashSet<Identifier> newEquality = new HashSet<>();
        newEquality.add(a);
        newEquality.add(b);
        equalities.add(newEquality);
    }

    private void addEquality(Collection<Identifier> identifiers) {
        Identifier prev = null;
        for (Identifier identifier : identifiers) {
            if (prev != null) {
                addEquality(prev, identifier);
            }
            prev = identifier;
        }
    }

    private void reassign(Identifier a) {
        equalities.stream().filter(e -> e.contains(a)).findAny().ifPresent(equality -> equality.remove(a));
        equalities.add(new HashSet<>(Collections.singleton(a)));
    }

    public EqualityDomain() {
    }

    public EqualityDomain(EqualityDomain other) {
        for (var eq: other.equalities) {
            equalities.add(new HashSet<>(eq));
        }
    }


    @Override
    public boolean lessOrEqual(EqualityDomain other) throws SemanticException {
        return other.equalities.stream().allMatch(o -> equalities.stream().anyMatch(e -> e.containsAll(o)));
    }

    @Override
    public EqualityDomain lub(EqualityDomain other) throws SemanticException {
        if (isBottom()) {
            return other;
        }
        if (other.isBottom()) {
            return this;
        }
        EqualityDomain result = new EqualityDomain();
        var identifiers = equalities.stream().flatMap(Collection::stream).toArray(Identifier[]::new);
        for (var id: identifiers) {
            result.reassign(id);
        }

        for (var eq: equalities) {
            for (var o: other.equalities) {
                var copy = new HashSet<>(eq);
                copy.retainAll(o);
                result.addEquality(copy);
            }
        }
        return result;
    }

    @Override
    public EqualityDomain top() {
        return TOP;
    }

    @Override
    public boolean isTop() {
        return equalities.isEmpty();
    }

    @Override
    public EqualityDomain bottom() {
        return BOTTOM;
    }

    @Override
    public boolean isBottom() {
        return this == BOTTOM;
    }

    @Override
    public EqualityDomain assign(Identifier identifier, ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        EqualityDomain res = new EqualityDomain(this);
        if (valueExpression instanceof Identifier) {
            res.addEquality(identifier, (Identifier) valueExpression);
            return res;
        }

        res.reassign(identifier);
        return res;
    }

    @Override
    public EqualityDomain smallStepSemantics(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        return this;
    }

    @Override
    public EqualityDomain assume(ValueExpression valueExpression, ProgramPoint programPoint, ProgramPoint programPoint1, SemanticOracle semanticOracle) throws SemanticException {
        var res = satisfies(valueExpression, programPoint, semanticOracle);
        if (res == Satisfiability.SATISFIED) {
            return this;
        }
        if (res == Satisfiability.NOT_SATISFIED) {
            return bottom();
        }

        return this;
    }

    @Override
    public boolean knowsIdentifier(Identifier identifier) {
        return equalities.stream().anyMatch(e -> e.contains(identifier));
    }

    @Override
    public EqualityDomain forgetIdentifier(Identifier identifier) throws SemanticException {
        var res = new EqualityDomain(this);
        for (var eq: res.equalities) {
            eq.remove(identifier);
        }
        return res;
    }

    @Override
    public EqualityDomain forgetIdentifiersIf(Predicate<Identifier> predicate) throws SemanticException {
        var res = new EqualityDomain(this);
        var identifiers = equalities.stream().flatMap(Collection::stream).toArray(Identifier[]::new);
        for (var identifier: identifiers) {
            if (predicate.test(identifier)) {
                for (var eq: res.equalities) {
                    eq.remove(identifier);
                }
            }
        }
        return res;
    }

    @Override
    public Satisfiability satisfies(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        boolean inverted = false;
        if (valueExpression instanceof UnaryExpression) {
            UnaryExpression unary = (UnaryExpression) valueExpression;
            if (unary.getOperator() instanceof LogicalNegation) {
                valueExpression = (ValueExpression) unary.getExpression();
                inverted = true;
            }
        }
        if (!(valueExpression instanceof BinaryExpression)) {
            return Satisfiability.UNKNOWN;
        }
        BinaryExpression binary = (BinaryExpression) valueExpression;
        if (!(binary.getOperator() instanceof ComparisonEq || binary.getOperator() instanceof ComparisonNe)) {
            return Satisfiability.UNKNOWN;
        }
        if (!(binary.getLeft() instanceof Identifier && binary.getRight() instanceof Identifier)) {
            return Satisfiability.UNKNOWN;
        }
        Identifier left = (Identifier) binary.getLeft();
        Identifier right = (Identifier) binary.getRight();
        return equalities.stream().anyMatch(eq -> eq.contains(left) && eq.contains(right)) ?
            inverted != binary.getOperator() instanceof ComparisonEq
                ? Satisfiability.SATISFIED
                : Satisfiability.NOT_SATISFIED
        : Satisfiability.UNKNOWN;
    }

    @Override
    public EqualityDomain pushScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }

    @Override
    public EqualityDomain popScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }

    @Override
    public StructuredRepresentation representation() {
        return new StringRepresentation(
            isBottom() ? "⊥" :
            String.join(", ",
                equalities.stream()
                    .map(eq -> String.join(" = ", eq.stream().map(Identifier::getName).toArray(String[]::new)))
                    .toArray(String[]::new)
            )
        );
    }
}
