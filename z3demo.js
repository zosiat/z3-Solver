import { init } from 'z3-solver';

const { Context } = await init();
const { Solver, Int, Distinct, And, Not, Or } = new Context("main");
const solver = new Solver();

//integer values
const Bob = Int.const('Bob');
const Mary = Int.const('Mary');
const Cathy = Int.const('Cathy');
const Sue = Int.const('Sue');

//pet constraints
const CAT = 1;
const DOG = 2;
const BIRD = 3;
const FISH = 4;

//clues
solver.add(Bob.eq(DOG));                //bob has the dog
solver.add(Sue.eq(BIRD));               //sue has the bird
solver.add(Or(Mary.eq(CAT), Mary.eq(DOG), Mary.eq(BIRD))); //mary does not have a fish

//each child has a unique pet
solver.add(Distinct(Bob, Mary, Cathy, Sue));

//each child must choose from available pet options
const pets = [CAT, DOG, BIRD, FISH];
solver.add(And(
    pets.includes(Bob),
    pets.includes(Mary),
    pets.includes(Cathy),
    pets.includes(Sue)
));

//run Z3 solver
const result = await solver.check();
if (result === "sat") {
    const model = solver.model();
    const bobPet = model.eval(Bob).value();
    const maryPet = model.eval(Mary).value();
    const cathyPet = model.eval(Cathy).value();
    const suePet = model.eval(Sue).value();

    //map pet values to names for clarity
    const petNames = { 1: "Cat", 2: "Dog", 3: "Bird", 4: "Fish" };

    console.log("Solution:");
    console.log(`Bob has ${petNames[bobPet]}`);
    console.log(`Mary has ${petNames[maryPet]}`);
    console.log(`Cathy has ${petNames[cathyPet]}`);
    console.log(`Sue has ${petNames[suePet]}`);
} else {
    console.log("No solution found.");
}
