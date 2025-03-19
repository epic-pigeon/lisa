package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.SemanticDomain;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.*;
import it.unive.lisa.symbolic.value.operator.binary.*;
import it.unive.lisa.symbolic.value.operator.unary.NumericNegation;
import it.unive.lisa.symbolic.value.operator.unary.UnaryOperator;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

public final class CongruenceDomain implements BaseNonRelationalValueDomain<CongruenceDomain> {
    private static int lcm(int a, int b) {
        if (a == 0 || b == 0) {
            return 0;
        }
        return (a * b) / gcd(a, b);
    }

    private static int gcd(int a, int b) {
        if (b == 0) {
            return a;
        } else {
            return gcd(b, a % b);
        }
    }

    private static final class GCDResult {
        public final int gcd, x, y;

        public GCDResult(int gcd, int x, int y) {
            this.gcd = gcd;
            this.x = x;
            this.y = y;
        }
    }

    private static GCDResult extendedGCD(int a, int b) {
        if (a == 0) {
            return new GCDResult(b, 0, 1);
        } else {
            GCDResult result = extendedGCD(b % a, a);
            return new GCDResult(
                result.gcd,
                result.y - (b / a) * result.x,
                result.x
            );
        }
    }

    private static boolean divides(int a, int b) {
        return a != 0 && b % a == 0 || a == 0 && b == 0;
    }

    private static boolean eqModulo(int a, int b, int m) {
        return divides(m, Math.abs(a - b));
    }


    private final int coeff, offset;

    public static final CongruenceDomain TOP = new CongruenceDomain(1, 0);
    public static final CongruenceDomain BOTTOM = new CongruenceDomain(Integer.MIN_VALUE, Integer.MIN_VALUE);

    public CongruenceDomain() {
        this(1, 0);
    }

    public CongruenceDomain(int coeff, int offset) {
        this.coeff = Math.abs(coeff);
        this.offset = coeff == 0 ? offset : ((offset % coeff) + coeff) % coeff;
    }

    public int getCoeff() {
        return coeff;
    }

    public int getOffset() {
        return offset;
    }

    @Override
    public boolean lessOrEqualAux(CongruenceDomain other) throws SemanticException {
        return divides(other.coeff, coeff) && eqModulo(offset, other.offset, other.coeff);
    }

    @Override
    public CongruenceDomain lubAux(CongruenceDomain other) throws SemanticException {
        return new CongruenceDomain(
            gcd(gcd(coeff, other.coeff), Math.abs(offset - other.offset)),
            other.offset
        );
    }

    @Override
    public CongruenceDomain glbAux(CongruenceDomain other) throws SemanticException {
        return
            eqModulo(offset, other.offset, gcd(coeff, other.coeff)) ?
                new CongruenceDomain(
                    lcm(coeff, other.coeff),
                    extendedGCD(coeff, other.coeff).x * coeff + offset
                )
            :
                bottom();
    }

    @Override
    public CongruenceDomain narrowingAux(CongruenceDomain other) throws SemanticException {
        return coeff == 1 ? other : this;
    }

    @Override
    public CongruenceDomain evalNonNullConstant(Constant constant, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (constant.getValue() instanceof Integer) {
            return new CongruenceDomain(0, (int) constant.getValue());
        } else {
            return top();
        }
    }

    @Override
    public CongruenceDomain evalUnaryExpression(UnaryOperator operator, CongruenceDomain arg, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (operator == NumericNegation.INSTANCE) {
            return new CongruenceDomain(arg.coeff, -arg.offset);
        }
        return top();
    }

    @Override
    public CongruenceDomain evalBinaryExpression(BinaryOperator operator, CongruenceDomain left, CongruenceDomain right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (left.isBottom() || right.isBottom()) {
            return bottom();
        }

        if (operator instanceof AdditionOperator) {
            return new CongruenceDomain(
                gcd(left.coeff, right.coeff),
                left.offset + right.offset
            );
        }
        if (operator instanceof SubtractionOperator) {
            return new CongruenceDomain(
                gcd(left.coeff, right.coeff),
                left.offset - right.offset
            );
        }
        if (operator instanceof MultiplicationOperator) {
            return new CongruenceDomain(
                gcd(left.coeff * right.coeff, gcd(left.coeff * right.offset, right.coeff * left.offset)),
                left.offset * right.offset
            );
        }
        if (operator instanceof DivisionOperator) {
            if (right.coeff == 0 && right.offset == 0) {
                return bottom();
            }
            if (right.coeff == 0 && divides(right.offset, left.coeff) && divides(right.offset, left.offset)) {
                return new CongruenceDomain(
                    left.coeff / right.offset,
                    left.offset / right.offset
                );
            }
            return top();
        }
        if (operator instanceof RemainderOperator) {
            if (right.coeff == 0 && right.offset == 0) {
                return bottom();
            }
            if (right.coeff == 0 && divides(right.offset, left.coeff)) {
                return new CongruenceDomain(
                    0,
                    left.offset % right.offset
                );
            }
            return top();
        }
        return top();
    }

    private Satisfiability inverse(Satisfiability s) {
        if (s == Satisfiability.SATISFIED) {
            return Satisfiability.NOT_SATISFIED;
        }
        if (s == Satisfiability.NOT_SATISFIED) {
            return Satisfiability.SATISFIED;
        }
        return Satisfiability.UNKNOWN;
    }

    @Override
    public Satisfiability satisfiesBinaryExpression(BinaryOperator operator, CongruenceDomain left, CongruenceDomain right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (left.isBottom() || right.isBottom()) {
            return Satisfiability.UNKNOWN;
        }

        if (operator instanceof ComparisonEq) {
            if (left.glb(right).isBottom()) {
                return Satisfiability.NOT_SATISFIED;
            }
            if (left.lessOrEqualAux(right) && right.lessOrEqualAux(left)) {
                return Satisfiability.SATISFIED;
            }
            return Satisfiability.UNKNOWN;
        }
        if (operator instanceof ComparisonNe) {
            return inverse(satisfiesBinaryExpression(ComparisonEq.INSTANCE, left, right, pp, oracle));
        }
        if (left.coeff != 0 || right.coeff != 0) {
            return Satisfiability.UNKNOWN;
        }
        if (operator instanceof ComparisonGt) {
            return left.offset > right.offset ? Satisfiability.SATISFIED : Satisfiability.NOT_SATISFIED;
        }
        if (operator instanceof ComparisonGe) {
            return left.offset >= right.offset ? Satisfiability.SATISFIED : Satisfiability.NOT_SATISFIED;
        }
        if (operator instanceof ComparisonLt) {
            return left.offset < right.offset ? Satisfiability.SATISFIED : Satisfiability.NOT_SATISFIED;
        }
        if (operator instanceof ComparisonLe) {
            return left.offset <= right.offset ? Satisfiability.SATISFIED : Satisfiability.NOT_SATISFIED;
        }

        return Satisfiability.UNKNOWN;
    }

    @Override
    public CongruenceDomain top() {
        return TOP;
    }

    @Override
    public CongruenceDomain bottom() {
        return BOTTOM;
    }

    @Override
    public StructuredRepresentation representation() {
        return new StringRepresentation(coeff + "Z+" + offset);
    }

    @Override
    public boolean isTop() {
        return coeff == 1;
    }
}
