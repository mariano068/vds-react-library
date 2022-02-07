import { ReactJSXElement } from '@emotion/react/types/jsx-namespace';
import { ExpandLess, ExpandMore } from '@mui/icons-material';
import ChevronLeftIcon from '@mui/icons-material/ChevronLeft';
import MenuIcon from "@mui/icons-material/Menu";
import { Collapse } from '@mui/material';
import Divider from '@mui/material/Divider';
import MuiDrawer from '@mui/material/Drawer';
import List from '@mui/material/List';
import ListItem from '@mui/material/ListItem';
import ListItemIcon from '@mui/material/ListItemIcon';
import ListItemText from '@mui/material/ListItemText';
import { styled } from '@mui/material/styles';
import * as React from 'react';
import { Fragment } from 'react';
import { BsCircle } from 'react-icons/bs';
import { VdsTooltip } from '../VdsTooltip/VdsTooltip';

export interface MenuNode {
    id: string;
    module: string;
    name_en: string;
    name_it: string;
    parent: string;
}

export type AdaptedMenuConfig = {
    onClick?: (ev: any, item: AdaptedMenuNode) => void;
    icon?: React.ReactElement | ReactJSXElement;
    title: (menuNode: MenuNode) => any;
}

export interface AdaptedMenuNode extends MenuNode {
    childrens?: AdaptedMenuNode[];
    config?: AdaptedMenuConfig;
}

export interface MenuNode {
    id: string;
    level: number;
    module: string;
    parent: string;
}

export interface AdaptedMenuNode extends MenuNode {
    childrens?: AdaptedMenuNode[];
    config?: AdaptedMenuConfig;
}

const drawerWidth = 250;

const activeMenuStyleWithoutChildrens = {
    'level_1': {
        backgroundImage: "linear-gradient(90deg, #0090D1, #00C3EA)",
        color: "white",
        ":hover": {
            opacity: "0.8",
        },
    },
    'level_2': {
        backgroundColor: "#e4eaf0",
        color: "#0090D1!important",
        'svg': {
            fill: "#0090D1!important",
            color: "#0090D1!important"
        },
        ":hover": {
            opacity: "0.9",
            background: "#e4eaf0!important",
            color: "#0090D1!important",
        },
    },
    'level_3': {
        backgroundColor: "#f2f5f8",
        color: "#0090D1!important",
        ":hover": {
            opacity: "0.9",
            backgroundColor: "#f2f5f8",
            color: "#0090D1",
        },
        "svg": {
            fill: "#0090D1!important"
        }
    }
}

const itemStyle = {
    'level_1': {
        backgroundColor: "#152935",
        color: "white",
        letterSpacing: "0.25px",
        textAlign: "left",
        lineHeight: "20px",
        fontFamily: "Roboto",
        fontWeight: 400,
        '.MuiDrawer-paper': { color: '#152935' },
        'svg': { fill: `white!important`, color: 'white!important' },
        ":hover": {
            opacity: "0.9",
        },
    },
    'level_2': {
        backgroundColor: "#e4eaf0",
        color: "#005075",
        letterSpacing: "0.25px",
        textAlign: "left",
        lineHeight: "20px",
        fontFamily: "Roboto",
        fontWeight: 400,
        '.MuiDrawer-paper': { color: 'black' },
        'svg': { fill: `#005075!important`, color: '#005075!important' },
        ":hover": {
            opacity: "0.9",
            backgroundColor: "#e4eaf0",
            color: "#005075",
        },
    },
    'level_3': {
        backgroundColor: "#f2f5f8",
        color: "black!important",
        letterSpacing: "0.25px",
        textAlign: "left",
        lineHeight: "20px",
        fontFamily: "Roboto",
        fontWeight: 400,
        '.MuiDrawer-paper': { color: 'black' },
        'svg': { fill: `black`, color: 'black' },
        ":hover": {
            opacity: "0.9",
            backgroundColor: "#f2f5f8",
            color: "black!important",
        },
    }
}

const activeMenuStyleWithChildrens = {
    'level_1': {
        backgroundImage: "linear-gradient(90deg, #0090D1, #00C3EA)",
        color: "white",
        ":hover": {
            opacity: "0.9",
        },
    },
    'level_2': {
        backgroundColor: "#e4eaf0",
        color: "#0090D1!important",
        'svg': {
            fill: "#0090D1!important",
            color: "#0090D1!important"
        },
        ":hover": {
            opacity: "0.9",
            backgroundColor: "#e4eaf0",
            color: "#0090D1!important",
        },
    }
}

const openedMixin = () => ({
    width: drawerWidth,
    overflowX: 'hidden',
});

const closedMixin = () => ({
    overflowX: 'hidden',
    width: 55,
});

const checkActiveItem = (module: string | Array<MenuNode>, activeItem: any, level: number): any => {
    if (typeof module === 'string') return activeItem === module ? activeMenuStyleWithoutChildrens[`level_${level}`] : undefined;
    return module.find((ev: any) => ev.module === activeItem || ev.childrens?.length && ev.childrens.find((ev2: any) => ev2.module === activeItem)) ? activeMenuStyleWithChildrens[`level_${level}`] : undefined;
}

const Adapters = {
    menuNodeToAdaptedMenuNode: (configuration?: { [P in string]: AdaptedMenuConfig }) => {
        return (args: MenuNode) => ({
            ...args,
            childrens: [],
            config: configuration && configuration[args.module] || undefined
        }) as AdaptedMenuNode;
    }
}

const Test = ({ open }: any) => ({
    '.MuiDrawer-paper': {
        backgroundColor: '#152935',
        color: "white",
        borderColor: "white",
    },
    'svg': {
        fill: 'white',
        fontSize: '1.5rem'
    },
    '.MuiListItemIcon-root': {
        minWidth: 40
    },
    'span': {
        whiteSpace: 'pre-wrap'
    },
    flexShrink: 0,
    whiteSpace: 'nowrap',
    boxSizing: 'border-box',
    overflowY: 'hidden',
    //...(!open && {
    //    '*::-webkit-scrollbar': {
    //        width: '0'
    //    },
    //}),
    ...(open && {
        ...openedMixin(),
        '& .MuiDrawer-paper': openedMixin(),
    }),
    ...(!open && {
        ...closedMixin(),
        '& .MuiDrawer-paper': closedMixin(),
    })
});

const ScrollListStyle = ({ open }: any) => ({
    overflowY: 'auto',
    overflowX: 'hidden',
    ...(!open && {
        '::-webkit-scrollbar': {
            width: '0px !important'
        },
    })
});

const ListTest = styled(List, { shouldForwardProp: (prop: any) => prop !== 'open' } as any) as any;
const ScrollList = ListTest(ScrollListStyle) as any;

const DrawerTest = styled(MuiDrawer, { shouldForwardProp: (prop: any) => prop !== 'open' } as any) as any;
const Drawer = DrawerTest(Test) as any;

const MiniDrawerListItemWithTooltip = React.forwardRef(function MiniDrawerListItemWithTooltip(props: any, ref: any) {
    const { module, icon, onClick, setActiveItem, activeItem, level, ...other } = props;
    return (
        <ListItem
            {...other}
            button
            ref={ref}
            sx={{
                ...checkActiveItem(module, activeItem, level) || itemStyle[`level_${level}`],
                minHeight: 48
            }}
            onClick={() => {
                onClick && onClick(props);
                setActiveItem(module);
            }}
        >
            <ListItemIcon>{icon ?? <BsCircle style={{ fontSize: 23 }} />}</ListItemIcon>
        </ListItem>
    );
});
const MiniDrawerListItemWithChildTooltip = React.forwardRef(function MiniDrawerListItemWithChildTooltip(props: any, ref: any) {
    const { icon, id, childrens, onClick } = props;
    const { accordionState, handleAccordionClose, activeItem, level, ...other } = props;
    return (
        <ListItem
            {...other}
            button
            onClick={() => {
                onClick && onClick(props);
                handleAccordionClose(true)
            }}
            ref={ref}
            sx={{
                ...checkActiveItem(childrens, activeItem, level) || itemStyle[`level_${level}`],
                minHeight: 48
            }}
        >
            <ListItemIcon>{icon ?? <BsCircle style={{ fontSize: 23 }} />}</ListItemIcon>
            {accordionState === id ? <ExpandLess /> : <ExpandMore />}
        </ListItem>
    );
});
const MiniDrawerListItem: React.VFC<any> = (item) => {
    const { icon, onClick, title } = item.config || {};
    const { module, drawerState, setActiveItem, activeItem, level } = item;
    if (drawerState) {
        return (
            <ListItem
                button
                onClick={() => {
                    onClick && onClick(item);
                    setActiveItem(module);
                }}
                sx={checkActiveItem(module, activeItem, level) || itemStyle[`level_${level}`]}
            >
                <ListItemIcon>{ level !== 3 && (icon ?? <BsCircle style={{ fontSize: 23 }} />)}</ListItemIcon>
                <ListItemText primary={title ? title(item) : module} />
            </ListItem>
        );
    }
    return (
        <VdsTooltip arrow title={title ? title(item) : module} placement="right">
            <MiniDrawerListItemWithTooltip
                activeItem={activeItem}
                module={module}
                setActiveItem={setActiveItem}
                icon={icon}
                level={level}
                onClick={onClick}
            />
        </VdsTooltip>
    );
}
const MiniDrawerListItemWithChild: React.VFC<any> = (item) => {
    const { icon, onClick, title } = item.config || {};
    const { module, id, childrens, drawerState, handleAccordionClose, accordionState, activeItem, level } = item;
    if (drawerState) {
        return (
            <ListItem
                button
                onClick={() => {
                    onClick && onClick(item);
                    handleAccordionClose(true)
                }}
                sx={checkActiveItem(childrens || [], activeItem, level) || itemStyle[`level_${level}`]}
            >
                <ListItemIcon>{level !== 3 && (icon ?? <BsCircle style={{ fontSize: 23 }} />)}</ListItemIcon>
                <ListItemText primary={title ? title(item) : module} />
                {accordionState ? <ExpandLess /> : <ExpandMore />}
            </ListItem>
        );
    }
    return (
        <VdsTooltip arrow title={title ? title(item) : module} placement="right">
            <MiniDrawerListItemWithChildTooltip
                module={module}
                icon={icon}
                id={id}
                level={level}
                activeItem={activeItem}
                accordionState={accordionState}
                handleAccordionClose={handleAccordionClose}
                onClick={onClick}
                childrens={childrens}
            />
        </VdsTooltip>
    );
}

const MenuNodeChildrensList = ({ item, drawerState, activeItem, setActiveItem }: any) => {

    const [accordionState, setAccordionState] = React.useState<boolean>(true);

    const handleAccordionClose = () => { setAccordionState(!accordionState) };

    return (
        <Fragment>
            <MiniDrawerListItemWithChild
                {...item}
                activeItem={activeItem}
                drawerState={drawerState}
                handleAccordionClose={handleAccordionClose}
                accordionState={accordionState}
            />
            <Collapse
                in={accordionState}
                timeout="auto"
                unmountOnExit
            >
                <List component="div" disablePadding>
            {item.childrens?.map((item: any, j: any) => {
                        return (
                            <MenuNodeList
                                menuNodes={[item]}
                                drawerState={drawerState}
                                activeItem={activeItem}
                                setActiveItem={setActiveItem}
                                key={`child-${j}`}
                            />
                        );
                    })}
                </List>
            </Collapse>
        </Fragment>
    );
};

const MenuNodeList = ({ menuNodes, drawerState, activeItem, setActiveItem }: any) => {

  return menuNodes.map((item: any, i: any) => {

        const { childrens } = item;

        if (childrens?.length) {
            return (
                <MenuNodeChildrensList
                    key={`child-${i}`}
                    item={item}
                    drawerState={drawerState}
                    activeItem={activeItem}
                    setActiveItem={setActiveItem}
                />
            );
        }
        return (
            <MiniDrawerListItem
                drawerState={drawerState}
                activeItem={activeItem}
                setActiveItem={setActiveItem}
                key={`item-${i}`}
                {...item}
            />
        );
    });
}

/**
 * Crea un albero, fino ad un massimo di 4 livelli
 * @param mn menunodes
 * @param configuration configuration
 */
const menuNodesToDrawerAdapter = (menuNodes: MenuNode[], configuration?: { [P in string]: AdaptedMenuConfig }) => {

    const _menuNodes: AdaptedMenuNode[] = menuNodes.map(Adapters.menuNodeToAdaptedMenuNode(configuration));
    const drawer_adapted_array: AdaptedMenuNode[] = _menuNodes.filter(({ parent }) => !parent.includes('_'));

    drawer_adapted_array.forEach((fst_ch) => {

        const snd_lv_chls = _menuNodes.filter((snd_ch) => {

            const isFstChld = snd_ch.parent === fst_ch.id;

            if (isFstChld) {

                const thd_lv_chls = _menuNodes.filter((thd_ch) => {

                    const isSndChld = thd_ch.parent === snd_ch.id;

                    if (isSndChld) {

                        const fth_lv_chls = _menuNodes.filter((fth_ch) => {
                            const x = fth_ch.parent === thd_ch.id
                            if (x) fth_ch.level = 4;
                            return x;
                        });

                        thd_ch.level = 3;
                        if (fth_lv_chls.length) {
                            thd_ch.childrens = fth_lv_chls;
                        }
                    }
                    return isSndChld;
                });

                snd_ch.level = 2;
                if (thd_lv_chls.length) {
                    snd_ch.childrens = thd_lv_chls;
                }
            }
            return isFstChld;
        });

        fst_ch.level = 1;
        if (snd_lv_chls.length) {
            fst_ch.childrens = snd_lv_chls;
        }
    });

    return drawer_adapted_array;
};

export const VdsDrawer: React.FC<{ menuNodes: MenuNode[], configuration?: { [P in string]: AdaptedMenuConfig } }> = (props) => {

    const { configuration, children } = props;

    const [drawerState, setDrawerState] = React.useState<boolean>(true);
    const [activeItem, setActiveItem] = React.useState<string>('');

    React.useEffect(() => {

        // Seleziona home come primo elemento di default se non è definito un modulo Home, usa il primo figlio disponibile e triggera il click se definito
        const check_home_module = menuNodes.find(({ module }) => String(module).toLowerCase() === 'home');

        if (check_home_module) {
            const { childrens, module } = check_home_module;
            // se home è un raggruppamento seleziona il primo figlio disponibile
            if (childrens?.length) {
                setActiveItem(childrens[0].module);
                if (childrens[0]?.config?.onClick) childrens[0].config?.onClick(null, check_home_module);
                return;
            }
            setActiveItem(module);
            if (check_home_module.config?.onClick) check_home_module.config?.onClick(null, check_home_module);
            return;
        } else {

            const { childrens, module } = menuNodes[0];
            // se item è un raggruppamento seleziona il primo figlio disponibile
            if (childrens?.length) {
                setActiveItem(childrens[0].module);
                if (childrens[0]?.config?.onClick) childrens[0].config?.onClick(null, childrens[0]);
                return;
            }
            setActiveItem(module);
            if (menuNodes[0].config?.onClick) menuNodes[0].config?.onClick(null, menuNodes[0]);
            return;
        }

    }, []);

    const handleDrawerOpen = () => { setDrawerState(true); };
    const handleDrawerClose = () => { setDrawerState(false); };

    const menuNodes = menuNodesToDrawerAdapter(props.menuNodes, configuration);

    return (
        <div style={{ display: "flex", height: '100%' }}>
            <div style={{ height: '100%' }}>
                <Drawer variant="permanent" open={drawerState}>
                    <List disablePadding>
                        <ListItem
                            style={{
                                display: "flex",
                                justifyContent: "flex-end",
                                margin: "4px 0",
                            }}
                        >
                            <ListItemIcon
                                style={{
                                    display: "contents",
                                    color: "white",
                                    cursor: "pointer",
                                }}
                                onClick={drawerState ? handleDrawerClose : handleDrawerOpen}
                            >
                                {drawerState ? <ChevronLeftIcon /> : <MenuIcon />}
                            </ListItemIcon>
                        </ListItem>
                    </List>
                    <Divider style={{ backgroundColor: "white" }} />
                    <ScrollList open={drawerState} disablePadding>
                        <MenuNodeList
                            menuNodes={menuNodes}
                            drawerState={drawerState}
                            activeItem={activeItem}
                            setActiveItem={setActiveItem}
                        />
                    </ScrollList>
                </Drawer>
            </div>
            <div style={{
                flexGrow: 1,
                padding: "16px"
            }}>
                {children}
            </div>
        </div>
    );
}
