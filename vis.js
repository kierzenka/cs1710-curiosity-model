const stage = new Stage();

const randomColor = () => {
    return Math.floor(Math.random() * 16777215).toString(16);
}

const states = instance.signature('State').atoms();
const poles = instance.signature('Pole').atoms();
const rings = instance.signature('Ring').atoms();

const ringColors = [];
for (let i = 0; i < rings.length; i++) {
    ringColors.push('#' + randomColor());
}

const stateHeight = 180;
const startingPosition = { x: 100, y: 100 };
const poleBaseWidth = 160;
const poleBaseHeight = 10;
const poleWidth = 10;
const poleHeight = 80;
const poleSpacing = 20;
const ringHeight = poleBaseWidth / 10;
const ringBaseWidth = 20;

// stage.add(new TextBox(`${poles[0].join(instance.field('top'))}`, {x:100, y:100},'black',16));

// iterate over states
for (let stateNum = 0; stateNum < states.length; stateNum++) {
    const currState = instance.signature('State').atom(`State${stateNum}`);

    for (let poleNum = 0; poleNum < poles.length; poleNum++) {
        const poleBaseLeft = startingPosition.x + (poleBaseWidth + poleSpacing) * poleNum;
        const poleTop = startingPosition.y + stateNum * stateHeight;

        // pole
        stage.add(new Rectangle(poleHeight, poleWidth, { x: poleBaseLeft + poleBaseWidth / 2 - poleWidth / 2, y: poleTop }, 'black'));

        // pole base
        stage.add(new Rectangle(poleBaseHeight, poleBaseWidth, { x: poleBaseLeft, y: poleTop + poleHeight }, 'black'))

        // if pole has a ring, get all rings by iterating through field 'underMe' until no rings left
        // todo: get all rings on the pole and stick em in this array
        const currPole = instance.signature('Pole').atom(`Pole${poleNum}`)
        const topRing = currState.join(currPole.join(top))

        stage.add(new TextBox(topRing, { x: 100, y: 100 }, 'black', 16));

        const ringsOnThisPole = [];

        for (let ringIdx = ringsOnThisPole.length; ringIdx >= 0; ringIdx--) {
            // todo: finalize visualization when able to get rings
            // increase height with each subsequent ring
            // stage.add(new Rectangle(ringHeight, ringBaseWidth * ring.radius, {x: poleBaseLeft + poleBaseWidth / 2 - ring.radius * ringBaseWidth, y: poleTop + poleHeight - ringHeight * ringIdx}))
        }
    }
}

stage.render(svg, document)