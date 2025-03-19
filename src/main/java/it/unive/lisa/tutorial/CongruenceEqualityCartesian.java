package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.combination.CartesianProduct;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;

public class CongruenceEqualityCartesian
    extends CartesianProduct<CongruenceEqualityCartesian, EqualityDomain, ValueEnvironment<CongruenceDomain>, ValueExpression, Identifier>
    implements ValueDomain<CongruenceEqualityCartesian>
{
    public CongruenceEqualityCartesian() {
        this(new EqualityDomain(), new ValueEnvironment<>(new CongruenceDomain()));
    }

    public CongruenceEqualityCartesian(EqualityDomain left, ValueEnvironment<CongruenceDomain> right) {
        super(left, right);
    }

    @Override
    public CongruenceEqualityCartesian mk(EqualityDomain equalityDomain, ValueEnvironment<CongruenceDomain> congruenceDomain) {
        return new CongruenceEqualityCartesian(equalityDomain, congruenceDomain);
    }

    @Override
    public boolean knowsIdentifier(Identifier identifier) {
        return left.knowsIdentifier(identifier);
    }
}
