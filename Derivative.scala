package DerivativeCalculator
// enumerations 
enum Op(val value:String):
    case plus extends Op(" + ")
    case minus extends Op(" - ")
    case multiply extends Op(" * ")
    case divide extends Op(" / ")
    case rb extends Op ("(")
    case lb extends Op(")")
    case ^ extends Op(" ^ ")
    case raisePower extends Op("^")
// helper functions
implicit def IntToDifferentiable(value:Int):constantDiff = constantDiff(value)
implicit def StringToDifferentiable(value:String):variableDiff = variableDiff(value)
implicit def ConstantToInt(value:constantDiff):Int = value.coefficient
def derive(expression:differentiable):differentiable =  expression.differentiate()
trait differentiable()  {
    // override apply so that some simplification can happen as the derivative is
    val coefficient:Int
    def multiplyCoeff(factor:Int):differentiable
    def setCoeff1():differentiable
    def setCoeff0():differentiable
    def differentiate():differentiable
    def + (right : differentiable,sign:Op = Op.plus):additiveDiff= additiveDiff(this,right,Op.plus)
    // match on constant+constant X+X  and aX+bX when X are like terms.
    // introduce commutivity by (a+b)+c should create a sequence 
    def - (right : differentiable):additiveDiff = additiveDiff(this,right,Op.minus)
    def ^ (right:differentiable):powerDiff= powerDiff(this,right)
    infix def toThePowerOf (right:differentiable):powerDiff=powerDiff(this,right)
    def * (right : differentiable): multiplicativeDiff =  {
        val product = this.coefficient * right.coefficient
        multiplicativeDiff(this.setCoeff1(),right.setCoeff1(),product)
    }
    def / (right : differentiable): divisionDiff =  divisionDiff(this,right)
    infix def dividedBy (right:differentiable):divisionDiff=divisionDiff(this,right)
    protected def wrap(value:String):String = "(" + value + ")"
    protected def showCoeff(expression:String):String={
        if (this.coefficient == 1){
            expression
        }
        else if (this.coefficient == 0){
            // variables with coefficents of 0 should be dealt with later on in the code
            "(0)"
        }
        else{
            this.coefficient.toString() + this.wrap(expression.toString())
        }
    }
}
trait functonDiff()extends differentiable{
    val functionAsString:String
    override protected def showCoeff(expression: String): String = {
        if this.coefficient == 1 then
            functionAsString + this.wrap(expression)
        else
            this.coefficient.toString()+ functionAsString + this.wrap(expression)
    }
}
case class additiveDiff(a:differentiable,b:differentiable,c:Op,override val coefficient:Int=1) extends  differentiable{

    val firstValue = a
    val secondValue = b
    val sign = c
    //def simplify  a(x)+b(x) = (a+b)(x)
    def multiplyCoeff(factor:Int):additiveDiff = copy(coefficient = coefficient*factor)
    def decrementCoeff():additiveDiff = copy(coefficient = coefficient-1)
    def setCoeff0(): additiveDiff = copy(coefficient = 0)
    def setCoeff1(): additiveDiff = copy(coefficient = 1)
    def differentiate(): differentiable = {
        return additiveDiff(firstValue.differentiate(),secondValue.differentiate(),sign).multiplyCoeff(this.coefficient)
    }
    override def toString(): String =this.showCoeff( firstValue.toString() + sign.value + secondValue.toString())
}
case class multiplicativeDiff(a:differentiable,b:differentiable,override val coefficient:Int=1)extends differentiable{
    val firstValue = a
    val secondValue = b
    // copy a and b and reset their coeffcients to 1. this class should have their product
    //def simplify x^a * x^b = x^(a+b)

    def multiplyCoeff(factor:Int):multiplicativeDiff = copy(coefficient = coefficient*factor)
    def decrementCoeff():multiplicativeDiff = copy(coefficient = coefficient-1)
    def setCoeff0(): multiplicativeDiff = copy(coefficient = 0)
    def setCoeff1(): multiplicativeDiff = copy(coefficient = 1)
    def differentiate():differentiable={
        val firstDiff = firstValue.differentiate()*secondValue
        val secondDiff = firstValue * secondValue.differentiate()
        return (firstDiff + secondDiff).multiplyCoeff(this.coefficient)
    }
    override def toString(): String = this.showCoeff( firstValue.toString() + Op.multiply.value + secondValue.toString())
}
case class divisionDiff(a:differentiable,b:differentiable,override val coefficient:Int=1) extends differentiable{
    // coeffcient of the numerator and denominator should impact division coefficent in simplify
    b match
        case constantDiff(value) => 
            require(value!=0)
    // for symbolic differentiation this may not be a good idea to check this here
    // division by 0 symbolically might not be possible unless the original function 
    val numerator = a
    val denonminator = b
    def multiplyCoeff(factor:Int):divisionDiff = copy(coefficient = coefficient*factor)
    def decrementCoeff():divisionDiff = copy(coefficient = coefficient-1)
    def setCoeff0(): divisionDiff = copy(coefficient = 0)
    def setCoeff1(): divisionDiff = copy(coefficient = 1)
    def differentiate(): differentiable = {
        val newNum = numerator.differentiate()*denonminator - numerator*denonminator.differentiate()
        val newDen = denonminator toThePowerOf 2
        return divisionDiff(newNum,newDen)
    }

    override def toString(): String = this.showCoeff(numerator.toString())  + Op.divide.value + this.wrap( denonminator.toString())

}
case class powerDiff(a:differentiable, b:differentiable,override val coefficient:Int=1)extends differentiable{
    val base = a
    val pow = b
    //def simplify():differentiable // will likely need monadic operations. want to check for pow = 1 or 0.
    // if it is a constant to the power of constant might want to wrap the differential in a constant class
    // might make it so that expressions multiplied by constants just become the expression with changed coefficient
    def multiplyCoeff(factor:Int):powerDiff = copy(coefficient = coefficient*factor)
    def decrementCoeff():powerDiff = copy(coefficient = coefficient-1)
    def setCoeff0(): powerDiff = copy(coefficient = 0)
    def setCoeff1(): powerDiff = copy(coefficient = 1)
    override def showCoeff(expression:String):String={
        if (this.coefficient == 1){
            this.wrap(expression.toString())
        }
        else if (this.coefficient == 0){
            // variables with coefficents of 0 should be dealt with later on in the code
            "(0)"
        }
        else{
            this.coefficient.toString() + this.wrap(expression.toString())
        }
    }
    def differentiate(): differentiable = {
        base match
            case constantDiff(a) => lnDiff(a)*this.copy()*pow.differentiate()
             // if the exponent is a constant the function is multiplied by 0
             case _=> pow match // otheriwise match on exponent. the base is not a constant
                case constantDiff(2)=>base.multiplyCoeff(2)*base.differentiate()
                case constantDiff(b)=> powerDiff(base,b-1).multiplyCoeff(b)*base.differentiate()
                case _ => this.copy() * (lnDiff(base)*pow).differentiate()        
    }
    override def toString(): String = this.showCoeff( base.toString()) + Op.raisePower.value + pow.toString()
}
case class lnDiff(expression:differentiable,override val coefficient:Int=1)extends functonDiff{
    val functionAsString: String = "ln"
    def multiplyCoeff(factor:Int):lnDiff = copy(coefficient = coefficient*factor)
    def decrementCoeff():lnDiff = copy(coefficient = coefficient-1)
    def setCoeff0(): lnDiff = copy(coefficient = 0)
    def setCoeff1(): lnDiff = copy(coefficient = 1)
    def differentiate(): differentiable = { // could abstract the idea of chain rule in the functionDiff trait
        powerDiff(expression,-1)*expression.differentiate()
    }
}
case class constantDiff(val coefficient:Int=1)extends differentiable{ // constant can instead be 1 with varying coefficient values
    val value = coefficient
    def multiplyCoeff(factor:Int):constantDiff = copy(coefficient = coefficient*factor)
    def decrementCoeff():constantDiff = copy(coefficient = coefficient-1)
    def setCoeff0(): constantDiff = copy(coefficient = 0)
    def setCoeff1(): constantDiff = copy(coefficient = 1)
    def differentiate(): differentiable = {
        return constantDiff(0)
    }
    override def toString(): String = value.toString()
}
case class variableDiff(a:String="x", val coefficient:Int=1) extends differentiable{ // for now all variables are treated the same
    def multiplyCoeff(factor:Int):variableDiff = copy(coefficient = coefficient*factor)
    def decrementCoeff():variableDiff = copy(coefficient = coefficient-1)
    def setCoeff0(): variableDiff = copy(coefficient = 0)
    def setCoeff1(): variableDiff = copy(coefficient = 1)
    def differentiate(): differentiable = constantDiff(1) // only if the variable is the same as what its differentiated in respect to
    override def toString(): String = showCoeff(a)
}
@main def main(): Unit = {
    val xSquared = (variableDiff("x") toThePowerOf 2)
    val function1 = xSquared.multiplyCoeff(2)
    val function2 = xSquared.multiplyCoeff(3)
    val function4 = function1*function2
    val function3 = (xSquared.multiplyCoeff(2) + 1) toThePowerOf 2
    val function5 = lnDiff(xSquared)
    Console.println(function4)
    Console.println(function4.differentiate())
}
