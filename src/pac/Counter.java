package pac;


/**
 * Provide a counter for a participant in the simulation.
 * This includes an identifying string and a count of how
 * many participants of this type currently exist within 
 * the simulation.
 * 
 * @author David J. Barnes and Michael Kolling
 * @version 2003.10.28
 */
public class Counter
{
    // A name for this type of simulation participant
    private /*@ nullable spec_public @*/ String name;
    // How many of this type exist in the simulation.
    private /*@ spec_public @*/ int count;

    /**
     * Provide a name for one of the simulation types.
     * @param name  A name, e.g. "Shark".
     */
    public Counter(String name)
    {
        this.name = name;
        count = 0;
    }
    
    /**
     * @return The short description of this type.
     */
    public String getName()
    {
        return name;
    }

    /**
     * @return The current count for this type.
     */
    public int getCount()
    {
        return count;
    }

    /**
     * Increment the current count by one.
     */
    public void increment()
    {
        count++;
    }
    
    /**
     * Reset the current count to zero.
     */
    public void reset()
    {
        count = 0;
    }
}
