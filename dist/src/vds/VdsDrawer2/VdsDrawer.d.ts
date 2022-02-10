import { ReactJSXElement } from '@emotion/react/types/jsx-namespace';
import * as React from 'react';
export interface MenuNode {
    id: string;
    module: string;
    name_en: string;
    name_it: string;
    parent: string;
}
export declare type AdaptedMenuConfig = {
    onClick?: (ev: any, item: AdaptedMenuNode) => void;
    icon?: React.ReactElement | ReactJSXElement;
    title: (menuNode: MenuNode) => any;
};
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
export declare const VdsDrawer: React.FC<{
    menuNodes: MenuNode[];
    configuration?: {
        [P in string]: AdaptedMenuConfig;
    };
}>;
