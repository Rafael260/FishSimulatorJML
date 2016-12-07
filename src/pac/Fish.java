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
    protected /*@ nullable spec_public @*/ Random random;
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
        random = new Random();
        isAlive = true;
        nivelEnergia = 15;
        age = 0;
        this.maxAge = maxAge;
        this.campo = campo;
        pos_linha = linha;
        pos_coluna = coluna;
        campo.colocarAtor(this, getLocation());
    }
    
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
    @Override
    public /*@ pure @*/ boolean isAlive() {
        return this.isAlive;
    }
    
    /**
     * 
     * @return a idade do ator
     */
    public /*@ pure @*/ int getAge() {
        return age;
    }

    public void setAge(int age) {
        this.age = age;
    }

    @Override
    public /*@ pure @*/ int getLinha() {
        return pos_linha;
    }

    @Override
    public void setLinha(int pos_linha) {
        this.pos_linha = pos_linha;
    }

    @Override
    public /*@ pure @*/ int getColuna() {
        return pos_coluna;
    }

    @Override
    public void setColuna(int pos_coluna) {
        this.pos_coluna = pos_coluna;
    }
    
    public int getEnergia(){
    	return this.nivelEnergia;
    }
    
	public Location getLocation() {
		return campo.getLocation(pos_linha, pos_coluna);
	}
    
    @Override
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
    //@ensures \result >= 10 && \result < maxFood;
    public int inicializaFome(int maxFood){
        return random.nextInt(maxFood - 10) + 10;
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
    public void incrementAge(int maxAge) throws MorteException{
        age++;
        if (age > maxAge)
            throw new MorteException();
    }
    /**
     * Diminui 1 da fome, se zerar, seta morto
     */
    // ensures nivelEnergia == \old(nivelEnergia) - 1;
    // ensures (nivelEnergia <= 0) ==> !this.isAlive;
    
    
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
    //@requires newLocation != null;
    //@requires Field.saoAdjacentes(getLocation(),newLocation);
    //@ ensures campo.getAtor(newLocation).equals(this);
    // ensures campo.getAtor(\old(pos_linha),\old(pos_coluna)) == null;
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
    //@ ensures \result >= 0;
    //@ ensures \result <= maxFilhos;
    public int numeroDeFilhos(int idadeMinima, double probabilidade, int maxFilhos){
        int numFilhos = 0;
        if (podeTerFilho(idadeMinima) && random.nextDouble() <= probabilidade){
            numFilhos = random.nextInt(maxFilhos) + 1;
        }
        return numFilhos;
    }
}
