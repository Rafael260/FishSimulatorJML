package pac;

import java.util.Random;

import exceptions.MorteException;


/**
 * Write a description of class Fish here.
 * 
 * NOTE: This should serve as a superclass to all specific tyes of fish
 * 
 * @author (your name) 
 * @version (a version number or a date)
 */
public abstract class Fish implements Actor
{
    protected /*@ spec_public @*/ boolean isAlive; //@ in isActive;
    protected /*@ spec_public @*/ int age; //@ in ageOf;
    protected /*@ spec_public @*/ int nivelEnergia;
    protected /*@ spec_public @*/ int pos_linha; //@ in row;
    protected /*@ spec_public @*/ int pos_coluna; //@ in col;
    protected /*@ spec_public @*/ Field campo;
    protected /*@ spec_public @*/ int maxAge;
    
    /**
     * Constructor for objects of class Fish
     */
    public Fish(Field campo, int linha, int coluna, int maxAge)
    {
    	isAlive = true;
        nivelEnergia = 15;
        age = 0;
        this.maxAge = maxAge;
        this.campo = campo;
        pos_linha = linha;
        pos_coluna = coluna;
        campo.colocarAtor(this, getLocation());
    }
    
    //@public initially (isAlive && age == 0 && nivelEnergia == 15);
    
    //@public invariant campo.estaNoIntervalo(pos_linha,pos_coluna);
    
    /*@ protected represents
      @ isActive = this.isAlive;
      @*/
    /*@ protected represents
    @ ageOf = this.age;
    @*/
    /*@ protected represents
    @ row = this.pos_linha;
    @*/
    /*@ protected represents
    @ col = this.pos_coluna;
    @*/
    
    /**
     * Funcao para saber se o ator esta vivo
     */
    //@also
    //@assignable \nothing;
    //@ensures \result == isActive;
    @Override
    public /*@ pure @*/ boolean isAlive() {
        return this.isAlive;
    }
    
    /**
     * 
     * @return a idade do ator
     */
    //@also
    //@assignable \nothing;
    //@ensures \result == ageOf;
    public /*@ pure @*/ int getAge() {
        return age;
    }

    //@assignable age;
    //@ensures this.age == age;
    public void setAge(int age) {
        this.age = age;
    }

    @Override
    //@also
    //@assignable \nothing;
    //@ensures \result == row;
    public /*@ pure @*/ int getLinha() {
        return pos_linha;
    }

    @Override
    //@also
    //@assignable this.pos_linha;
    //@ensures this.pos_linha == pos_linha;
    public void setLinha(int pos_linha) {
        this.pos_linha = pos_linha;
    }

    @Override
    //@also
    //@assignable \nothing;
    //@ensures \result == this.pos_coluna;
    public /*@ pure @*/ int getColuna() {
        return pos_coluna;
    }

    @Override
    //@also
    //@assignable this.pos_coluna;
    //@ensures this.pos_coluna == pos_coluna;
    public void setColuna(int pos_coluna) {
        this.pos_coluna = pos_coluna;
    }
    
    //@also
    //@assignable \nothing;
    //@ensures \result == this.nivelEnergia;
    @Override
    public int getEnergia(){
    	return this.nivelEnergia;
    }
    
    //@also
    //@assignable \nothing;
    //@ensures \result == campo.getLocation(pos_linha, pos_coluna);
	@Override
    public Location getLocation() {
		return campo.getLocation(pos_linha, pos_coluna);
	}
    
    @Override
    //@also
    //@assignable \nothing;
    //@ensures \result ==> (this.isAlive == ator.isAlive() && this.age == ator.getAge() && this.pos_linha == ator.getLinha() && this.pos_coluna == ator.getColuna());
	public /*@ pure @*/ boolean equals(Actor ator) {
		return this.isAlive == ator.isAlive() && this.age == ator.getAge() && this.pos_linha == ator.getLinha() && this.pos_coluna == ator.getColuna();
	}
    
    //@ assignable isAlive;
    //@ ensures !this.isAlive;
    //Garante que o campo em que o ator ocupava estara disponivel para outros atores
    //@ensures this.campo.getLocation(pos_linha, pos_coluna).getAtor() == null;
    /**
     * Esvazia a posicao que o ator estava e marca como morto, para ser excluido da lista
     */        
    public void setMorto(){
    	isAlive = false;
    	campo.limparPosicao(getLocation());
    }
    
    /**
     * Inicia a fome de forma aleatoria
     */
    //@requires maxFood > 0;
    //@assignable nivelEnergia;
    //@ensures nivelEnergia >= 10 && nivelEnergia < maxFood;
    public void inicializarFome(int maxFood){
        Random random = new Random();
    	this.nivelEnergia = random.nextInt(maxFood - 10) + 10;
    }
    
    /*@   public normal_behavior
    @ 		requires age < maxAge;
    @  	assignable age;
    @  	ensures age == \old(age) + 1;
    @  also
    @    public exceptional_behavior
    @  	requires age == maxAge;
    @  	assignable age;
    @		signals_only MorteException;
    @		signals (MorteException e)
    @			age > maxAge;
    @*/
    //@assignable age;
    public void incrementAge(int maxAge) throws MorteException{
        age++;
        if (age > maxAge)
            throw new MorteException();
    }    
    
    /*@   public normal_behavior
     @ 		requires nivelEnergia > 1;
     @  	assignable nivelEnergia;
     @  	ensures nivelEnergia == \old(nivelEnergia) - 1;
     @  also
     @    public exceptional_behavior
     @  	requires nivelEnergia == 1;
     @  	assignable nivelEnergia;
     @		signals_only MorteException;
     @		signals (MorteException e)
     @			nivelEnergia == 0;
     @ 
     @*/
    //@assignable nivelEnergia;
    public void decrementaNivelFome() throws MorteException{
        nivelEnergia--;
        if (nivelEnergia == 0){
            throw new MorteException();
        }
    }
    
    /**
     * O ator chama esse metodo quando encontra comida, aumenta seu nivel da energia
     */
    //@ requires valor >= 0;
    //@ requires maxFood > 0;
    //@ assignable nivelEnergia;
    //@ ensures nivelEnergia >= \old(nivelEnergia);
    //@ ensures nivelEnergia <= maxFood;
    public void alimenta(int valor, int maxFood){
        nivelEnergia += valor;
        if (nivelEnergia > maxFood){
            nivelEnergia = maxFood;
        }   
    }
    
    /**
     * Move o ator de posicao no tabuleiro
     */
    //@ requires newLocation != null;
    //@ requires Field.saoAdjacentes(getLocation(),newLocation);
    //@ assignable pos_linha, pos_coluna;
    //@ ensures campo.getAtor(newLocation).equals(this);
    //@ ensures campo.getAtor(\old(getLocation())) == null;
    public void mover(Location newLocation){
        Location oldLocation = getLocation();
    	campo.colocarAtor(this, newLocation);
        pos_linha = newLocation.getLinha();
        pos_coluna = newLocation.getColuna();
        campo.limparPosicao(oldLocation);
    }
    
    //@ requires idadeMinima >= 0;
    //@ ensures \result ==> (this.age >= idadeMinima);
    /**
     * Metodo usado para saber quando o ator pode ter filho
     */
    public boolean podeTerFilho(int idadeMinima){
        return age >= idadeMinima;
    }

    /**
     * Metodo responsavel para dizer quantos filhos um ator podera ter num determinado momento
     * e usado um randomico
     */
    //@ requires idadeMinima >= 0;
    //@ requires probabilidade >= 0.0 && probabilidade <= 1.0;
    //@ requires maxFilhos > 0;
    //@ assignable \nothing;
    //@ ensures \result >= 0;
    //@ ensures \result <= maxFilhos;
    public /*@ pure @*/ int numeroDeFilhos(int idadeMinima, double probabilidade, int maxFilhos){
        Random random = new Random();
    	int numFilhos = 0;
        if (podeTerFilho(idadeMinima) && random.nextDouble() <= probabilidade){
            numFilhos = random.nextInt(maxFilhos) + 1;
        }
        return numFilhos;
    }
}
