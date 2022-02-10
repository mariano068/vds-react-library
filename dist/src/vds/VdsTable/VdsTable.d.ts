import * as React from 'react';
declare type Data<R = {}> = R[];
export declare type AsyncDataResult<R = {}> = {
    totalCount: number;
    data: Data<R>;
};
export declare type Query = {
    page?: number;
    pageSize?: number;
    search?: string;
    sorting?: any;
    columnsSearch?: any;
};
export declare type AsyncData<R = {}> = (query?: Query) => Promise<AsyncDataResult<R>>;
declare type SortingProps = {
    default?: 'Asc' | 'Desc';
    field: string;
};
declare type ColumnType<R = {}> = {
    title?: string;
    field?: keyof R;
    render?: (data: R) => any;
    sorting?: SortingProps;
    tooltip?: string | ((data: R) => string);
    search?: {
        field: string;
        type: 'text';
    } | {
        field: string;
        type: 'select';
        options: {
            text: string;
            value: string | null;
        }[];
    };
} & BaseColumnStyle;
declare type BaseColumnStyle = {
    width?: any;
    style?: any;
    thStyle?: any;
};
export declare type Column<R = {}> = ColumnType<R> | ColumnAction<R>;
declare type ColumnAction<R = {}> = {
    title?: string;
    tooltip: string;
    icon: React.ReactElement;
    onClick: (data: R, queryProps?: Query) => void;
} & BaseColumnStyle;
export declare type Action = {
    tooltip: string;
    icon: React.ReactElement;
    disabled?: boolean;
    disableIfEmpty?: boolean;
    onClick: (ev: any, queryProps: Query) => any;
};
interface VdsTableConfig<R = {}> {
    pagination: {
        usePagination?: boolean;
        rowsPerPageOptions?: number[];
        rowsPerPage?: number;
        defaultPageSize?: number;
    };
    height?: string;
    maxHeight?: string;
    adjustHeader?: number;
    onRowSelected?: (data: R) => boolean;
    search?: {
        useSearch: boolean;
        placeholder: string;
    };
    localize?: {
        noData?: string;
        search?: string;
        rowsForPage?: string;
        displayedElementsSeparator?: string;
    };
}
export interface VdsTableProps<R = {}> {
    /**
     * Set di dati utilizzabili per il popolamento dei dati nella tabella.
     * Nota: possono essere recuperati da una promise o da un'array
     **/
    data: Data<R> | AsyncData<R>;
    /**
     * Set di configurazioni utilizzate per la creazione delle celle nella tabella.
     **/
    columns: Column<R>[];
    /**
     *  Set di actions da utilizzare nell'intestazione della tabella
     **/
    actions?: (Action | null)[];
    /**
     *  Pannello di dettaglio
     * */
    initialize?: Query;
    /**
     *  Pannello di dettaglio
     * */
    detailPanel?: (data: R[]) => React.ReactElement;
    /**
     *  Gestione degli eventi
     * */
    events?: {
        onRowClick?: (row: R, queryProps: Query) => void;
    };
    config?: VdsTableConfig<R>;
    ref?: React.ForwardedRef<any>;
}
declare function VdsTable1<R = {}>(props: VdsTableProps<R>, ref: React.ForwardedRef<any>): JSX.Element;
export declare const VdsTable: <R>(props: VdsTableProps<R> & {
    ref?: ((instance: any) => void) | React.MutableRefObject<any> | null | undefined;
}) => ReturnType<typeof VdsTable1>;
export {};
