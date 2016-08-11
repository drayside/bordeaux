
sig Platform {}
sig Man {ceiling, floor: Platform}


pred diffPlatform[platform: set Platform, platform': set Platform, platform'': set Platform] {
    platform != platform' implies (platform'' = platform' - platform and platform'' + platform = platform') else no platform''
}

pred diffMan[man: set Man, man': set Man, man'': set Man] {
    man != man' implies (man'' = man' - man and man'' + man = man') else no man''
}

pred diffMan_ceiling[man_ceiling: Man->Platform, man_ceiling': Man->Platform, man_ceiling'': Man->Platform] {
    man_ceiling != man_ceiling' implies (man_ceiling'' = man_ceiling' - man_ceiling and man_ceiling'' + man_ceiling = man_ceiling') else no man_ceiling''
}

pred diffMan_floor[man_floor: Man->Platform, man_floor': Man->Platform, man_floor'': Man->Platform] {
    man_floor != man_floor' implies (man_floor'' = man_floor' - man_floor and man_floor'' + man_floor = man_floor') else no man_floor''
}

pred structuralConstraints [platform: set Platform, man: set Man, man_ceiling: Man->Platform, man_floor: Man->Platform] {
    (all p_this: one man | (one (p_this . man_ceiling) && ((p_this . man_ceiling) in platform)))
    ((man_ceiling . univ) in man)
    (all p_this: one man | (one (p_this . man_floor) && ((p_this . man_floor) in platform)))
    ((man_floor . univ) in man)
}

pred includeInstance [platform: set Platform, man: set Man, man_ceiling: Man->Platform, man_floor: Man->Platform] {
    (man_ceiling.Platform) in Man
    (Man.man_ceiling) in Platform
    (man_floor.Platform) in Man
    (Man.man_floor) in Platform
}

pred isInstance [platform: set Platform, man: set Man, man_ceiling: Man->Platform, man_floor: Man->Platform] {
    includeInstance[Platform, Man, man_ceiling, man_floor]
    structuralConstraints[Platform, Man, man_ceiling, man_floor]
}

pred findMarginalInstances[] {
    some platform, platform', platform'': set Platform, man, man', man'': set Manman_ceiling, man_ceiling', man_ceiling'': set Man->Platform, man_floor, man_floor', man_floor'': set Man->Platform | {
            (
            isInstance[platform, manman_ceiling, man_floor]
            and not isInstance[platform', man'man_ceiling', man_floor']
            and deltaPlatform[platform, platform', platform'']
            and deltaMan[man, man', man'']
            and deltaMan_ceiling[man_ceiling, man_ceiling', man_ceiling'']
            and deltaMan_floor[man_floor, man_floor', man_floor'']
            )
        and
            all platform1, platform1', platform1'': set Platform, man1, man1', man1'': set Manman_ceiling1, man_ceiling1', man_ceiling1'': set Man->Platform, man_floor1, man_floor1', man_floor1'': set Man->Platform | {
                    (
                    isInstance[platform1, man1man_ceiling1, man_floor1]
                    and not isInstance[platform1', man1'man_ceiling1', man_floor1']
                    and deltaPlatform[platform1, platform1', platform1'']
                    and deltaMan[man1, man1', man1'']
                    and deltaMan_ceiling[man_ceiling1, man_ceiling1', man_ceiling1'']
                    and deltaMan_floor[man_floor1, man_floor1', man_floor1'']
                    )
                implies
                    (
                    )
            }
    }
}
