package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.combination.CartesianProduct;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;

public class CongruenceEqualityCartesian {}
/*    extends CartesianProduct<CongruenceEqualityCartesian, EqualityDomain, CongruenceDomain, ValueExpression, Identifier>
{
    public CongruenceEqualityCartesian() {
        this(new EqualityDomain(), new CongruenceDomain());
    }

    public CongruenceEqualityCartesian(EqualityDomain left, CongruenceDomain right) {
        super(left, right);
    }

    @Override
    public CongruenceEqualityCartesian mk(EqualityDomain equalityDomain, CongruenceDomain congruenceDomain) {
        return new CongruenceEqualityCartesian(equalityDomain, congruenceDomain);
    }

    @Override
    public boolean knowsIdentifier(Identifier identifier) {
        return left.knowsIdentifier(identifier);
    }
}*/
