import { Check, Close, CloseOutlined } from '@mui/icons-material';
import SearchIcon from '@mui/icons-material/Search';
import { CircularProgress, FormControl, IconButton, Input, ListItem, Menu, MenuItem, Select, Stack, styled } from '@mui/material';
import Pagination from '@mui/material/Pagination';
import Table from '@mui/material/Table';
import TableBody from '@mui/material/TableBody';
import TableCell from '@mui/material/TableCell';
import TableContainer from '@mui/material/TableContainer';
import TableHead from '@mui/material/TableHead';
import TableRow from '@mui/material/TableRow';
import * as React from 'react';
import { Fragment } from 'react';
import { BsCaretDownFill, BsFillCaretRightFill } from 'react-icons/bs';
import { FaSort, FaSortDown, FaSortUp } from 'react-icons/fa';
import { RiFilterLine } from 'react-icons/ri';
import { VdsSelect, VdsTextField, VdsTooltip } from '..';

const ContainerWithTooltip = React.forwardRef(function ContainerWithTooltip({ children, ...props }: any, ref: any) {
    //  Spread the props to the underlying DOM element.
    return <div {...props} ref={ref}>{children}</div>
});

const StyledInput = styled(Input)(({ disabled, readOnly, error }: any) => ({
    'border': disabled ? '1px solid #C1C1C4' : readOnly ? '1px solid #C1C1C4' : error ? '1px solid #D82829' : '1px solid #C9D9E8',
    'backgroundColor': (disabled || readOnly) ? '#FAFBFD' : '#F2F5F8',
    'padding': '7.5px 14px!important',
    'font': 'unset',
    'cursor': disabled ? 'not-allowed' : 'text!important',
    input: {
        padding: 0,
    },
    ':hover': {
        'border': disabled ? '1px solid #0090D1' : readOnly ? '1px solid #C1C1C4' : error ? '1px solid #D82829' : '1px solid #0090D1!important'
    },
    '::placeholder': {
        'fontSize': "14px!important",
        'color': (disabled || readOnly) ? "#C1C1C4" : "#9DA6AD",
        'lineHeight': "18px",
        'fontWeight': 400,
        'textAlign': "left"
    },
    '::before': {
        'all': 'unset'
    },
    '::after': {
        'all': 'unset'
    }
}));

type Data<R = {}> = R[];
export type AsyncDataResult<R = {}> = { totalCount: number; data: Data<R>; }
export type Query = { page?: number; pageSize?: number; search?: string; sorting?: any; columnsSearch?: any }
export type AsyncData<R = {}> = (query?: Query) => Promise<AsyncDataResult<R>>

type SortingProps = { default?: 'Asc' | 'Desc', field: string };
type ColumnType<R = {}> = {
    // Titolo da usare per l'intestazione
    title?: string;
    field?: keyof R;
    // Restituisce il contenuto da utilizzare nella cella
    render?: (data: R) => any;
    // La colonna e' ordinabile
    sorting?: SortingProps;
    tooltip?: string | ((data: R) => string);
    // custom search
    search?: {
        field: string,
        type: 'text'
    } | {
        field: string,
        type: 'select',
        options: { text: string, value: string | null }[]
    }
} & BaseColumnStyle;

type BaseColumnStyle = {
    width?: any,
    style?: any,
    thStyle?: any
};

export type Column<R = {}> = ColumnType<R> | ColumnAction<R>;

type ColumnAction<R = {}> = {
    title?: string,
    tooltip: string,
    icon: React.ReactElement,
    onClick: (data: R, queryProps?: Query) => void
} & BaseColumnStyle;

export type Action = {
    tooltip: string,
    icon: React.ReactElement,
    disabled?: boolean,
    disableIfEmpty?: boolean,
    onClick: (ev: any, queryProps: Query) => any
}

interface VdsTableConfig<R = {}> {
    // Abilita/disabilita la paginazione
    pagination: {
        usePagination?: boolean;
        rowsPerPageOptions?: number[];
        rowsPerPage?: number;
        defaultPageSize?: number;
    },
    height?: string,
    maxHeight?: string,
    adjustHeader?: number,
    onRowSelected?: (data: R) => boolean,
    // abilita/disabilita il campo di ricerca
    search?: {
        useSearch: boolean;
        placeholder: string;
    },
    localize?: {
        noData?: string,
        search?: string,
        rowsForPage?: string,
        displayedElementsSeparator?: string,
    }
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
        onRowClick?: (row: R, queryProps: Query) => void
    },
    config?: VdsTableConfig<R>,

    ref?: React.ForwardedRef<any>
}

function AsyncDataTypeGuard(data: Data | AsyncData): data is AsyncData {
    return typeof data === 'function';
}

function ColumnTypeGuard(column: any): column is ColumnAction {
    return column.onClick !== undefined;
}

function CustomSearch({ submit, searchConfig, initialize }: { initialize?: Query, submit: (search: string) => void, searchConfig: VdsTableConfig['search'] }, ref: React.ForwardedRef<any>) {

    const [search, setSearch] = React.useState<string>(initialize?.search ?? '');

    const handleSearchChange = (ev: React.ChangeEvent<HTMLInputElement>) => {
        setSearch(ev.target.value as string);
    }

    React.useImperativeHandle(ref, () => ({
        search
    }), [search]);

    return (
        <div style={{ display: 'flex', alignItems: 'center' }}>
            <StyledInput
                onChange={handleSearchChange}
                placeholder={searchConfig?.placeholder}
                size="small"
                value={search}
                onKeyPress={(event: any) => {
                  const _search = event.target.value;
                    if (event.key === 'Enter') {
                        setSearch(_search);
                        submit(_search);
                    }
                }}
                endAdornment={search && (<IconButton sx={{
                    padding: 0,
                    opacity: 0.3
                }}
                    onClick={() => {
                        setSearch('');
                        submit('');
                    }}
                ><Close fontSize="small" /></IconButton>)}
                style={{ borderRadius: 0, width: '450px', fontFamily: 'Roboto !important' }}
            />
            <IconButton
                sx={{
                    p: '8px',
                    color: 'white',
                    borderRadius: '0!important',
                    backgroundImage: 'linear-gradient(90deg, #0090D1, #00C3EA)'
                }}
                onClick={() => submit(search)}
            >
                <SearchIcon />
            </IconButton>
        </div>
    );
}

const ReferencedCustomSearch = React.forwardRef(CustomSearch);

type VdsTableArgs<R> = {
    odata: R[];
    filteredData: R[];
    columnsSearch: { [P in keyof R]: any };
    data: R[];
    search: string;
    loader?: boolean;
    totalCount: number;
};

function getSortingMap(columns: Column<any>[], initialize?: Query) {

    if (initialize?.sorting) {

        let _osortingMap = {};
        let _sortingMap = { ...initialize.sorting };
        if (initialize?.sorting?.sort || initialize?.sorting?.order) {

            _sortingMap = { [initialize.sorting.sort]: initialize.sorting.order };
            _osortingMap = { [initialize.sorting.sort]: null };

        } else {
            for (let i in initialize.sorting) {

                _osortingMap[(i as any)] = null;
            }
        }

        return {
            sortingMap: _sortingMap,
            osortingMap: _osortingMap
        };
    } else {

        const defaultsortIsUnique = columns.filter((column) => {
            if (!ColumnTypeGuard(column)) {
                return (column as any).sorting?.default
            }
            return false;
        }).length <= 1;

        if (defaultsortIsUnique) {
            const _sortingMap = {};
            const _osortingMap = {};
            columns.forEach((column) => {
                if (!ColumnTypeGuard(column) && (column as any).sorting) {
                    _sortingMap[(column as any).sorting.field] = (column as any).sorting.default ?? null;
                    _osortingMap[(column as any).sorting.field] = null;
                }
            })

            return {
                sortingMap: _sortingMap,
                osortingMap: _osortingMap
            };
        } else {
          console.warn('Attenzione, non Ã¨ possibile configurare un ordinamento di default su piÃ¹ colonne');

          return {
            sortingMap: {},
            osortingMap: {}
          };
        }
    }
}

function htmlToText(html: any) {
    var temp = document.createElement('div');
    temp.innerHTML = html;
    return temp.textContent;
}

const byString = function (o: any, s: any) {
    s = s.replace(/\[(\w+)\]/g, '.$1'); // convert indexes to properties
    s = s.replace(/^\./, '');           // strip a leading dot
    var a = s.split('.');
    for (var i = 0, n = a.length; i < n; ++i) {
        var k = a[i];
        if (k in o) {
            o = o[k];
        } else {
            return;
        }
    }
    return o ? htmlToText(o) : '';
}

function CustomSelectFilter({ column, submit, initialize }: { config: VdsTableConfig<any>, column: { search: { options: any[], field: string } }, submit: any, initialize: any }) {

    const [state, setState] = React.useState(initialize ?? '');
    const [text, setText] = React.useState(initialize ? column.search.options.find(({ value }) => initialize === value)?.text : '');
    const [filterState, setFilterState] = React.useState(initialize ?? '');

    const [anchorEl, setAnchorEl] = React.useState(null);
    const open = Boolean(anchorEl);
  const handleClick = (event: any) => {
        setState(filterState);
        setAnchorEl(event.currentTarget);
    };
    const handleClose = () => {
        setAnchorEl(null);
        setState(filterState);
    };

    return (
        <div style={{
            display: 'flex',
            alignItems: 'center',
            cursor: 'pointer!important'
        }}>
            <div style={{
                flexGrow: 1,
                width: 'calc(100% - 70px)',
                display: 'flex',
                alignItems: 'center',
            }}>
                <Input
                    sx={{
                        ':before': {
                            'all': 'unset'
                        },
                        ':after': {
                            'all': 'unset'
                        },
                        border: 'unset',
                        width: "100%",
                        height: "100%",
                        padding: "0",
                        margin: "0",
                        boxSizing: 'border-box',
                        backgroundColor: '#F2F5F8'
                    }}
                    size="small"
                    placeholder="-"
                    readOnly
                    value={text}
                />
            </div>
            <div className='container'>
                {filterState && <IconButton onClick={(ev) => {
                    ev.stopPropagation();
                    setFilterState('');
                    submit({
                        field: column.search.field,
                        value: ''
                    })
                    setState('');
                    setText('');
                }}
                    sx={{
                        borderRadius: 'unset', ':hover': { backgroundColor: 'unset' },
                        padding: 0
                    }}
                >
                    <Close style={{ fill: '#0090D1', fontSize: '14px', opacity: 0.3 }} />
                </IconButton>}
                <IconButton onClick={handleClick} style={{ borderRadius: 'unset' }} >
                    <RiFilterLine style={{ fill: '#0090D1' }} />
                </IconButton>
            </div>
            <Menu
                sx={{
                    width: 162,
                }}
                anchorEl={anchorEl}
                open={open}
                onClose={handleClose}
            >
                <ListItem
                    sx={{
                        'div:first-of-type': {
                            minHeight: 'unset'
                        }
                    }}
                >
                    <VdsSelect
                        value={state ?? ''}
              onChange={(ev: any) => {
                            setState(ev.target.value);
                        }}
                        sx={{
                            width: 100,
                            '& div': {
                                minHeight: 0
                            }
                        }}
                    >
                        {column.search.options.map(({ text, value }, i) => {
                            return (
                                <MenuItem key={i} value={value ?? ''}>{text ?? '---'}</MenuItem>
                            );
                        })}
                    </VdsSelect>
                </ListItem>
                <ListItem
                    style={{ padding: '0 10px' }}
                >
                    <IconButton
                        size="small"
                        onClick={() => {
                            handleClose();
                            setState(filterState);
                            setText(column.search.options.find(({ value }) => filterState === value)?.text);
                        }}
                    >
                        <CloseOutlined />
                    </IconButton>
                    <IconButton
                        size="small"
                        onClick={() => {
                            setFilterState(state);
                            setText(column.search.options.find(({ value }) => state === value)?.text);
                            submit({
                                field: column.search.field,
                                value: state
                            })
                            handleClose();
                        }}
                    >
                        <Check />
                    </IconButton>
                </ListItem>
            </Menu>
        </div>
    );
}

function CustomTextFilter({ config, column, submit, initialize }: { config: VdsTableConfig<any>, column: { search: { options: any[], field: string } }, submit: any, initialize: any }) {

    const [state, setState] = React.useState(initialize ?? '');
    const [filterState, setFilterState] = React.useState(initialize ?? '');

    const [anchorEl, setAnchorEl] = React.useState(null);
    const open = Boolean(anchorEl);
  const handleClick = (event: any) => {
        setState(filterState);
        setAnchorEl(event.currentTarget);
    };
    const handleClose = () => {
        setAnchorEl(null);
        setState(filterState);
    };

    return (
        <div style={{
            display: 'flex',
            alignItems: 'center',
            cursor: 'pointer!important'
        }}>
            <div style={{
                flexGrow: 1,
                width: 'calc(100% - 70px)',
                display: 'flex',
                alignItems: 'center',
            }}>
                <Input
                    sx={{
                        ':before': {
                            'all': 'unset'
                        },
                        ':after': {
                            'all': 'unset'
                        },
                        border: 'unset',
                        width: "100%",
                        height: "100%",
                        padding: "0",
                        paddingLeft: '16px',
                        margin: "0",
                        boxSizing: 'border-box',
                        backgroundColor: '#F2F5F8'
                    }}
                    size="small"
                    placeholder="-"
                    readOnly
                    value={filterState}
                />
            </div>
            <div className='container'>
                {filterState && <IconButton onClick={(ev) => {
                    ev.stopPropagation();
                    setFilterState('');
                    setState('');
                    submit({
                        field: column.search.field,
                        value: ''
                    });
                }} sx={{
                    borderRadius: 'unset', ':hover': { backgroundColor: 'unset' },
                    padding: 0
                }}>
                    <Close style={{ fill: '#0090D1', fontSize: '14px', opacity: 0.3 }} />
                </IconButton>}
                <IconButton onClick={handleClick} style={{ borderRadius: 'unset' }} >
                    <RiFilterLine style={{ fill: '#0090D1' }} />
                </IconButton>
            </div>
            <Menu
                anchorEl={anchorEl}
                open={open}
                onClose={handleClose}
            >
                <ListItem
                    sx={{
                        'div:first-of-type': {
                            minHeight: 'unset'
                        }
                    }}
                >
                    <VdsTextField
                        value={state}
                        onChange={(ev) => setState(ev.target.value)}
                        fullWidth
                        inputProps={{
                            placeholder: config?.localize?.search || `Cerca`
                        }}
                    />
                </ListItem>
                <ListItem
                    style={{ padding: '0 10px' }}
                >
                    <IconButton
                        size="small"
                        onClick={() => {
                            handleClose();
                            setState(filterState);
                        }}
                    >
                        <CloseOutlined />
                    </IconButton>
                    <IconButton
                        size="small"
                        onClick={() => {
                            handleClose();
                            setFilterState(state);
                            submit({
                                field: column.search.field,
                                value: state
                            });
                        }}
                    >
                        <Check />
                    </IconButton>
                </ListItem>
            </Menu>
        </div>
    );
}

function VdsTable1<R = {}>(props: VdsTableProps<R>, ref: React.ForwardedRef<any>) {

    const { data, columns: _columns, config, actions, detailPanel, events, initialize } = props;

    // temporaneo per gestire i casi null
    const columns = _columns.filter((column) => column);

    const searchRef = React.useRef() || {
        current: {
            search: ''
        }
    };

    const [vdsTableArgs, setVdsTableArgs] = React.useState<VdsTableArgs<R>>({
        odata: [],
        filteredData: [],
        data: [],
        search: initialize?.search ?? '',
        totalCount: 0,
        loader: false,
        columnsSearch: initialize?.columnsSearch
    });
    const [sortingMap, setSortingMap] = React.useState<{
        sortingMap: { [p in string]: 'Asc' | 'Desc' | null },
        osortingMap: { [p in string]: 'Asc' | 'Desc' | null }
    }>(getSortingMap(columns, initialize));

    const [page, setPage] = React.useState<number>(initialize?.page ?? 1);
    const [pageSize, setPageSize] = React.useState<number>(initialize?.pageSize ?? config?.pagination?.defaultPageSize ?? 10);

    React.useEffect(() => {

        if (AsyncDataTypeGuard(data)) {

            const search = (searchRef?.current as any)?.search as string;

            const _map = sortingMap?.sortingMap
            const _sorting = { sort: null, order: null } as any;

            for (let o in _map) {

                if (_map[o]) {
                    _sorting.sort = o;
                    _sorting.order = _map[o];
                    break;
                }
            }

            setVdsTableArgs({
                ...vdsTableArgs,
                loader: true,
            });
            data({
                page,
                pageSize,
                search,
                sorting: _sorting,
                columnsSearch: vdsTableArgs?.columnsSearch
            })
                .then((result) => {
                    const { data, totalCount } = result;
                    setVdsTableArgs({
                        ...vdsTableArgs,
                        odata: data,
                        data,
                        loader: false,
                        search,
                        totalCount
                    });
                });
        }
    }, []);

    React.useEffect(() => {

        if (!AsyncDataTypeGuard(data)) {

            const search = vdsTableArgs?.search;

            const _map = sortingMap?.sortingMap
          const _sorting = { sort: null, order: null } as any;

            for (let o in _map) {

                if (_map[o]) {
                    _sorting.sort = o;
                    _sorting.order = _map[o];
                    break;
                }
            }

            const filteredData: any = data.sort((a: any, b: any) => {
                if (_sorting.order === 'Asc') {

                    const _srt = _sorting.sort.charAt(0).toLowerCase() + _sorting.sort.slice(1);
                    return String(a[_srt]).localeCompare(String(b[_srt]));
                } else if (_sorting.order === 'Desc') {

                    const _srt = _sorting.sort.charAt(0).toLowerCase() + _sorting.sort.slice(1);
                    return String(b[_srt]).localeCompare(String(a[_srt]));
                } else {

                    return a;
                }
            })

            const columnsSearch = {
                ...vdsTableArgs.columnsSearch
            };
            const _keys = Object.keys(columnsSearch);
            let _partialData = [...filteredData];

            if (vdsTableArgs?.search !== undefined && vdsTableArgs?.search !== null) {

                _partialData = filteredData.map((item: any) => {
                    let check = false;
                    for (let o in item) {
                        if (String(item[o]).toLowerCase().includes(vdsTableArgs.search.toLowerCase())) {
                            check = true;
                            break;
                        }
                    }
                    if (check) return item;
                    return null;
                }).filter((item: any) => item);
            }

            _keys.forEach((key) => {
                _partialData = _partialData.filter((el) => String(el[key]).toLowerCase().includes(columnsSearch[key].toLowerCase()));
            });

            setVdsTableArgs({
                ...vdsTableArgs,
                odata: data,
                filteredData: _partialData,
                data: _partialData.slice((page - 1) * pageSize, ((page - 1) * pageSize) + pageSize),
                search,
                columnsSearch,
                totalCount: _partialData.length
            });
        }
    }, [data]);

    React.useImperativeHandle(ref, () => ({
        reload: (): any => {

            const search = (searchRef?.current as any)?.search as string;

            if (AsyncDataTypeGuard(data)) {

                setVdsTableArgs({
                    ...vdsTableArgs,
                    loader: true,
                });
                const _map = sortingMap?.sortingMap
                const _sorting = { sort: null, order: null } as any;

                for (let o in _map) {

                    if (_map[o]) {
                        _sorting.sort = o;
                        _sorting.order = _map[o];
                        break;
                    }
                }

                return data({ page, pageSize, search, sorting: _sorting, columnsSearch: vdsTableArgs?.columnsSearch })
                    .then((result) => {
                        const { data, totalCount } = result;
                        setVdsTableArgs({
                            ...vdsTableArgs,
                            odata: data,
                            data,
                            search,
                            loader: false,
                            totalCount
                        });
                    });
            } else {

                console.error('Error: [useImperativeHandle] Si sta usando il metodo reload in un\'azione sincrona');
            }
        },
        totalCount: vdsTableArgs.totalCount,
        data: vdsTableArgs.filteredData,
        loader: (loader: boolean) => {

            setVdsTableArgs({
                ...vdsTableArgs,
                loader,
            });
        }
    }));

    const { totalCount } = vdsTableArgs;

    const handlePageChange = (_ev: unknown, _page: number) => {

        const search = (searchRef?.current as any)?.search as string;

        if (page === _page) return;

        if (AsyncDataTypeGuard(data)) {

            setVdsTableArgs({
                ...vdsTableArgs,
                loader: true,
            });
            const _map = sortingMap?.sortingMap;
            const _sorting = { sort: null, order: null } as any;

            for (let o in _map) {

                if (_map[o]) {
                    _sorting.sort = o;
                    _sorting.order = _map[o];
                    break;
                }
            }

            data({ page: _page, pageSize, search, sorting: _sorting, columnsSearch: vdsTableArgs?.columnsSearch })
                .then((result) => {
                    const { data, totalCount } = result;
                    setVdsTableArgs({
                        ...vdsTableArgs,
                        odata: data,
                        loader: false,
                        data,
                        totalCount
                    });
                    setPage(_page);
                });
        } else {

            const columnsSearch = {
                ...vdsTableArgs.columnsSearch
            };
            const _keys = Object.keys(columnsSearch);
            let _partialData = [...vdsTableArgs.odata];

            _keys.forEach((key) => {
                _partialData = _partialData.filter((el) => String(el[key]).toLowerCase().includes(columnsSearch[key].toLowerCase()));
            });

            setVdsTableArgs({
                ...vdsTableArgs,
                filteredData: _partialData,
                data: _partialData.slice((_page - 1) * pageSize, ((_page - 1) * pageSize) + pageSize),
            });
            setPage(_page);
        }
    };

    const handleChangeRowsPerPage = (event: React.ChangeEvent<HTMLInputElement>) => {

        const _pageSize = +event.target.value;
        const _page = 1;
        const search = (searchRef?.current as any)?.search as string;

        setPageSize(_pageSize);
        setPage(_page);

        if (AsyncDataTypeGuard(data)) {

            setVdsTableArgs({
                ...vdsTableArgs,
                loader: true,
            });
            const _map = sortingMap?.sortingMap;
            const _sorting = { sort: null, order: null } as any;

            for (let o in _map) {

                if (_map[o]) {
                    _sorting.sort = o;
                    _sorting.order = _map[o];
                    break;
                }
            }

            data({ page: _page, pageSize: _pageSize, search, sorting: _sorting, columnsSearch: vdsTableArgs?.columnsSearch })
                .then((result) => {
                    const { data, totalCount } = result;
                    setVdsTableArgs({
                        ...vdsTableArgs,
                        odata: data,
                        filteredData: data,
                        data,
                        loader: false,
                        totalCount
                    });
                });
        } else {

            const columnsSearch = {
                ...vdsTableArgs.columnsSearch
            };
            const _keys = Object.keys(columnsSearch);
            let _partialData = [...vdsTableArgs.odata];

            _keys.forEach((key) => {
                _partialData = _partialData.filter((el) => String(el[key]).toLowerCase().includes(columnsSearch[key].toLowerCase()));
            });

            setVdsTableArgs({
                ...vdsTableArgs,
                filteredData: _partialData,
                data: _partialData.slice((_page - 1) * _pageSize, ((_page - 1) * _pageSize) + _pageSize),
            });
        }
    };

    const VdsTablePagination: React.VFC<{ rowsPerPageOptions: number[] }> = ({ rowsPerPageOptions }) => {

        return (
            <div style={{ display: 'flex', alignItems: 'center', fontSize: '14px' }}>
                <p>
                    {config?.localize?.rowsForPage || 'Righe per pagina:'}
                </p>
                <FormControl
                    sx={{
                        'fieldset': {
                            border: 'unset'
                        }
                    }}
                >
                    <Select
                        value={pageSize}
                        style={{ fontSize: '14px' }}
                        onChange={handleChangeRowsPerPage as any}
                    >
                        {rowsPerPageOptions.map((value, i) => <MenuItem value={value} key={`menuitem-${i}`} style={{ fontSize: '14px' }}>{value}</MenuItem>)}
                    </Select>
                </FormControl>
                {vdsTableArgs?.loader && (
                    <>-</>
                )}
                {!vdsTableArgs?.loader && (
                    <p>
                        {pageSize >= totalCount ? totalCount : pageSize} {config?.localize?.displayedElementsSeparator || 'di'} {totalCount}
                    </p>
                )}
            </div>
        );
    }

    const Row: React.VFC<{ row: R } & { rowindex: number }> = ({ row, rowindex }) => {

        const [panel, setPanel] = React.useState<boolean>(false);

        if (detailPanel) {

            return (
                <Fragment>
                    <TableRow hover
                        sx={{
                            cursor: events?.onRowClick ? 'pointer' : 'text'
                        }}
                    >
                        {columns.map((column, i) => {

                            const { width, style } = column;

                            if (ColumnTypeGuard(column)) {

                                return (
                                    <TableCell key={`row-${rowindex}-cell-${i}`}
                                        sx={{
                                            cursor: 'pointer',
                                            width: width || 20,
                                            textAlign: 'center',
                                            paddingLeft: 0,
                                            paddingRight: 0,
                                            ...style
                                        }}>
                                        <VdsTooltip arrow title={column.tooltip}>
                                            <IconButton onClick={() => {

                                                const _map = sortingMap?.sortingMap;
                                                const _sorting = { sort: null, order: null } as any;

                                                for (let o in _map) {

                                                    if (_map[o]) {
                                                        _sorting.sort = o;
                                                        _sorting.order = _map[o];
                                                        break;
                                                    }
                                                }

                                                column.onClick(row, {
                                                    page,
                                                    pageSize,
                                                    search: vdsTableArgs.search,
                                                    sorting: _sorting,
                                                    columnsSearch: vdsTableArgs.columnsSearch
                                                })
                                            }} size="small" sx={style}>
                                                {column.icon}
                                            </IconButton>
                                        </VdsTooltip>
                                    </TableCell>
                                );
                            } else {

                                return (
                                    <TableCell
                                        key={`row-${rowindex}-cell-${i}`}
                                        sx={{
                                            ...(i === 0 ? {
                                                border: panel ? '1px solid #0090D1' : 'inital',
                                            } : {}),
                                            cursor: events?.onRowClick ? 'pointer' : 'text',
                                            width,
                                            ...style
                                        }}
                                    >
                                        {column?.tooltip ? (
                                            <VdsTooltip title={(column?.tooltip as any)(row)} placement="bottom" arrow>
                                                <ContainerWithTooltip
                                                    style={{
                                                        ...(i === 0 ? {
                                                            display: 'flex',
                                                            alignItems: 'center',
                                                        } : {})
                                                    }}
                                                >
                                                    {i === 0 && (
                                                        <IconButton
                                                            size="small"
                                                            onClick={() => {
                                                                setPanel(!panel);
                                                            }}
                                                        >
                                                            {panel ? <BsFillCaretRightFill /> : <BsCaretDownFill />}
                                                        </IconButton>
                                                    )}
                                                    <div
                                                        onClick={() => {
                                                            if (events?.onRowClick) {

                                                                const _map = sortingMap?.sortingMap;
                                                                const _sorting = { sort: null, order: null } as any;

                                                                for (let o in _map) {

                                                                    if (_map[o]) {
                                                                        _sorting.sort = o;
                                                                        _sorting.order = _map[o];
                                                                        break;
                                                                    }
                                                                }

                                                                events.onRowClick(row, {
                                                                    page,
                                                                    pageSize,
                                                                    search: vdsTableArgs.search,
                                                                    sorting: _sorting,
                                                                    columnsSearch: vdsTableArgs.columnsSearch
                                                                });
                                                            }
                                                        }}
                                                        style={style}
                                                    >
                                            {((column as ColumnType<R>)?.field && byString(row, (column as ColumnType<R>)?.field)) || ((column as ColumnType<R>)?.render && (column as any).render(row))}
                                                    </div>
                                                </ContainerWithTooltip>
                                            </VdsTooltip>
                                        ) : (
                                            <div
                                                style={{
                                                    ...(i === 0 ? {
                                                        display: 'flex',
                                                        alignItems: 'center',
                                                    } : {})
                                                }}
                                            >
                                                {i === 0 && (
                                                    <IconButton
                                                        size="small"
                                                        onClick={() => {
                                                            setPanel(!panel);
                                                        }}
                                                    >
                                                        {panel ? <BsFillCaretRightFill /> : <BsCaretDownFill />}
                                                    </IconButton>
                                                )}
                                                <div
                                                    onClick={() => {
                                                        if (events?.onRowClick) {

                                                            const _map = sortingMap?.sortingMap;
                                                            const _sorting = { sort: null, order: null } as any;

                                                            for (let o in _map) {

                                                                if (_map[o]) {
                                                                    _sorting.sort = o;
                                                                    _sorting.order = _map[o];
                                                                    break;
                                                                }
                                                            }

                                                            events.onRowClick(row, {
                                                                page,
                                                                pageSize,
                                                                search: vdsTableArgs.search,
                                                                sorting: _sorting,
                                                                columnsSearch: vdsTableArgs.columnsSearch
                                                            });
                                                        }
                                                    }}
                                                    style={style}
                                                >
                                            {((column as ColumnType<R>)?.field && byString(row, (column as ColumnType<R>)?.field)) || ((column as ColumnType<R>)?.render && (column as any).render(row))}
                                                </div>
                                            </div>
                                        )}
                                    </TableCell>
                                )
                            }
                        })}
                    </TableRow>
                    {panel && (
                        <TableRow key={`row-${rowindex}-cell-detail`} style={{
                            cursor: 'pointer'
                        }}>
                            <TableCell colSpan={columns.length} style={{
                                cursor: 'pointer'
                            }}>
                                {detailPanel(vdsTableArgs.data)}
                            </TableCell>
                        </TableRow>
                    )}
                </Fragment>
            );
        }

        return (
            <TableRow sx={(config?.onRowSelected && config?.onRowSelected(row)) ? {
                'td:first-of-type': {
                    borderLeft: '3px solid #0090D1',
                    borderTop: '1px solid #0090D1',
                    borderBottom: '1px solid #0090D1'
                },
                'td': {
                    borderTop: '1px solid #0090D1',
                    borderBottom: '1px solid #0090D1',
                },
                'td:last-child': {
                    borderTop: '1px solid #0090D1',
                    borderBottom: '1px solid #0090D1',
                    borderRight: '1px solid #0090D1',
                }
            } : {}} hover>
                {columns.map((column, i) => {

                    if (ColumnTypeGuard(column)) {

                        return (
                            <TableCell
                                key={`row-${rowindex}-cell-${i}`}
                                style={{
                                    wordBreak: 'break-all',
                                    ...column.style
                                }}
                            >
                                <VdsTooltip arrow title={column.tooltip}>
                                    <IconButton onClick={() => column.onClick(row)} size="small">
                                        {column.icon}
                                    </IconButton>
                                </VdsTooltip>
                            </TableCell>
                        );
                    } else {

                        return (
                            <TableCell
                                key={`row-${rowindex}-cell-${i}`}
                                style={{
                                    cursor: events?.onRowClick ? 'pointer' : 'text',
                                    wordBreak: 'break-all',
                                    ...column.style
                                }}
                                onClick={() => {
                                    if (events?.onRowClick) {

                                        const _map = sortingMap?.sortingMap;
                                        const _sorting = { sort: null, order: null } as any;

                                        for (let o in _map) {

                                            if (_map[o]) {
                                                _sorting.sort = o;
                                                _sorting.order = _map[o];
                                                break;
                                            }
                                        }

                                        events.onRowClick(row, {
                                            page,
                                            pageSize,
                                            search: vdsTableArgs.search,
                                            sorting: _sorting,
                                            columnsSearch: vdsTableArgs.columnsSearch
                                        });
                                    }
                                }}
                            >
                                {column?.tooltip ? (
                                    <VdsTooltip title={(column?.tooltip as any)(row)} placement="bottom" arrow>
                                        <ContainerWithTooltip>
                                  {((column as ColumnType<R>)?.field && byString(row, (column as ColumnType<R>)?.field)) || ((column as ColumnType<R>)?.render && (column as any).render(row))}
                                        </ContainerWithTooltip>
                                    </VdsTooltip>
                                ) : ((column as ColumnType<R>)?.field && byString(row, (column as ColumnType<R>)?.field)) || ((column as ColumnType<R>)?.render && (column as any).render(row))}
                            </TableCell>
                        )
                    }
                })}
            </TableRow>
        );
    }

    function ConditionalSorting({ column }: { column: Column }) {

        if (!ColumnTypeGuard(column) && sortingMap?.sortingMap && column.sorting?.field) {

            const sortState = sortingMap?.sortingMap[column.sorting.field];
            const callReload = (sorting: { [p in string]: string }) => {

                const search = (searchRef?.current as any)?.search as string;
                const _map = sorting
                const _sorting = { sort: null, order: null } as any;

                for (let o in _map) {

                    if (_map[o]) {
                        _sorting.sort = o;
                        _sorting.order = _map[o];
                        break;
                    }
                }

                if (AsyncDataTypeGuard(data)) {

                    setVdsTableArgs({
                        ...vdsTableArgs,
                        loader: true,
                    });
                    data({ page, pageSize, search, sorting: _sorting, columnsSearch: vdsTableArgs?.columnsSearch })
                        .then((result) => {
                            const { data, totalCount } = result;
                            setVdsTableArgs({
                                ...vdsTableArgs,
                                odata: data,
                                filteredData: data,
                                data,
                                loader: false,
                                search,
                                totalCount
                            });
                        });
                } else {

                    const filteredData: any = vdsTableArgs.odata.sort((a: any, b: any) => {
                        if (_sorting.order === 'Asc') {

                            const _srt = _sorting.sort.charAt(0).toLowerCase() + _sorting.sort.slice(1);
                            return String(a[_srt]).localeCompare(String(b[_srt]));
                        } else if (_sorting.order === 'Desc') {

                            const _srt = _sorting.sort.charAt(0).toLowerCase() + _sorting.sort.slice(1);
                            return String(b[_srt]).localeCompare(String(a[_srt]));
                        } else {

                            return a;
                        }
                    })

                    const columnsSearch = {
                        ...vdsTableArgs.columnsSearch,
                    };
                    const _keys = Object.keys(columnsSearch);
                    let _partialData = [...filteredData];

                    if (vdsTableArgs?.search !== undefined && vdsTableArgs?.search !== null) {

                        _partialData = filteredData.map((item: any) => {
                            let check = false;
                            for (let o in item) {
                                if (String(item[o]).toLowerCase().includes(vdsTableArgs.search.toLowerCase())) {
                                    check = true;
                                    break;
                                }
                            }
                            if (check) return item;
                            return null;
                        }).filter((item: any) => item);
                    }

                    _keys.forEach((key) => {
                        _partialData = _partialData.filter((el) => String(el[key]).toLowerCase().includes(columnsSearch[key].toLowerCase()));
                    });

                    setVdsTableArgs({
                        ...vdsTableArgs,
                        data: _partialData.slice((page - 1) * pageSize, ((page - 1) * pageSize) + pageSize),
                        search,
                        filteredData: _partialData,
                        totalCount: _partialData.length
                    });
                }
            }

            if (sortState === 'Asc')
                return (
                    <IconButton
                        size="small"
                        style={{ fontSize: '16px' }}
                        onClick={() => {

                            const _sortingMap = {
                                ...sortingMap.osortingMap,
                                [(column.sorting as any).field]: 'Desc'
                            };

                            setSortingMap({
                                ...sortingMap,
                                sortingMap: _sortingMap
                            });

                            callReload(_sortingMap);
                        }}
                    >
                        <FaSortDown style={{ fill: '#005075' }} />
                    </IconButton>
                );

            if (sortState === 'Desc')
                return (
                    <IconButton
                        size="small"
                        style={{ fontSize: '16px' }}
                        onClick={() => {

                            const _sortingMap = {
                                ...sortingMap.osortingMap,
                                [(column.sorting as any).field]: 'Asc'
                            }

                            setSortingMap({
                                ...sortingMap,
                                sortingMap: _sortingMap
                            });

                            callReload(_sortingMap);
                        }}
                    >
                        <FaSortUp style={{ fill: '#005075' }} />
                    </IconButton>
                );

            return (
                <IconButton
                    size="small"
                    style={{ fontSize: '16px' }}
                    onClick={() => {

                        const _sortingMap = {
                            ...sortingMap.osortingMap,
                            [(column.sorting as any).field]: 'Asc'
                        }

                        setSortingMap({
                            ...sortingMap,
                            sortingMap: _sortingMap
                        });

                        callReload(_sortingMap);
                    }}
                >
                    <FaSort style={{ fill: '#005075' }} />
                </IconButton>
            );
        }

        return null;
    }

    return (
        <div style={{ height: '100%', display: 'flex', flexDirection: 'column' }}>
            {config?.search?.useSearch && (
                <div>
                    <ReferencedCustomSearch
                        searchConfig={config?.search}
                        initialize={initialize}
                        ref={searchRef}
                        submit={(search) => {

                            const _page = 1;
                            const _pageSize = initialize?.pageSize ?? config?.pagination?.defaultPageSize ?? 10;
                            if (AsyncDataTypeGuard(data)) {

                                setVdsTableArgs({
                                    ...vdsTableArgs,
                                    loader: true,
                                });
                                const _map = sortingMap?.sortingMap;
                                const _sorting = { sort: null, order: null } as any;

                                for (let o in _map) {

                                    if (_map[o]) {
                                        _sorting.sort = o;
                                        _sorting.order = _map[o];
                                        break;
                                    }
                                }

                                setPage(_page);
                                setPageSize(_pageSize);

                                data({ page: _page, pageSize: _pageSize, search, sorting: _sorting, columnsSearch: vdsTableArgs?.columnsSearch })
                                    .then((result) => {
                                        const { data, totalCount } = result;
                                        setVdsTableArgs({
                                            ...vdsTableArgs,
                                            odata: data,
                                            filteredData: data,
                                            data,
                                            loader: false,
                                            search,
                                            totalCount
                                        });
                                    });
                            } else {

                                const filteredData: any = search ? vdsTableArgs.odata.map((item) => {
                                    let check = false;
                                    for (let o in item) {
                                        if (String(item[o]).toLowerCase().includes(search.toLowerCase())) {
                                            check = true;
                                            break;
                                        }
                                    }
                                    if (check) return item;
                                    return null;
                                }).filter((item) => item) : vdsTableArgs.odata;

                                const columnsSearch = {
                                    ...vdsTableArgs.columnsSearch,
                                };
                                const _keys = Object.keys(columnsSearch);
                                let _partialData = [...filteredData];

                                _keys.forEach((key) => {
                                    _partialData = _partialData.filter((el) => String(el[key]).toLowerCase().includes(columnsSearch[key].toLowerCase()));
                                });

                                setVdsTableArgs({
                                    ...vdsTableArgs,
                                    data: _partialData.slice((_page - 1) * _pageSize, ((_page - 1) * _pageSize) + _pageSize),
                                    search,
                                    filteredData: _partialData,
                                    totalCount: _partialData.length
                                });

                                setPage(_page);
                                setPageSize(_pageSize);
                            }
                        }}
                    />
                </div>
            )}
            {(actions?.length || config?.pagination?.usePagination) && (
                <div style={{ display: 'flex', alignItems: 'center', justifyContent: 'end', minHeight: '56px' }}>
                    {actions?.length && (
                        <Stack direction="row" spacing={2} sx={{ flexGrow: 1 }}>
                            {actions.map((action, j) => {
                                return action && (
                                    <VdsTooltip arrow title={action.tooltip} key={`action-${j}`}>
                                        <IconButton
                                            disabled={(action?.disableIfEmpty && !vdsTableArgs.data.length) || action?.disabled}
                                            onClick={(ev) => {
                                                const _map = sortingMap?.sortingMap;
                                                const _sorting = { sort: null, order: null } as any;

                                                for (let o in _map) {

                                                    if (_map[o]) {
                                                        _sorting.sort = o;
                                                        _sorting.order = _map[o];
                                                        break;
                                                    }
                                                }

                                                action.onClick(ev, {
                                                    page,
                                                    pageSize,
                                                    search: vdsTableArgs.search,
                                                    sorting: _sorting,
                                                    columnsSearch: vdsTableArgs.columnsSearch
                                                })
                                            }}
                                            size="small"
                                            sx={{ color: '#0090D1', width: '34px', height: '34px' }}
                                        >
                                            {action.icon}
                                        </IconButton>
                                    </VdsTooltip>
                                );
                            })}
                        </Stack>
                    )}
                    {config?.pagination?.usePagination && (
                        <VdsTablePagination rowsPerPageOptions={config?.pagination?.rowsPerPageOptions ?? [5, 10, 25]} />
                    )}
                </div>
            )}
            <TableContainer sx={{ height: config?.height, maxHeight: config?.maxHeight || 440, overflowX: 'hidden' }}>
                <Table stickyHeader size="small" style={{ tableLayout: 'fixed' }}>
                    <TableHead>
                        <TableRow>
                            {columns.filter(({ title }) => title).length && (
                                columns.map((column, ci) => (
                                    <TableCell
                                        key={`th-cell-${ci}`}
                                        sx={{
                                            fontSize: "14px",
                                            color: "#005075",
                                            lineHeight: "16px",
                                            fontFamily: "Roboto",
                                            fontWeight: 500,
                                            textAlign: "left",
                                            ...column.thStyle
                                        }}
                                    >
                                        <div
                                            style={{
                                                ...((column as any).sorting && {
                                                    display: 'flex',
                                                    alignItems: 'center'
                                                })
                                            }}
                                        >
                                            {column?.title}
                                            <ConditionalSorting column={column as any} />
                                        </div>
                                    </TableCell>
                                ))
                            )}
                        </TableRow>
                        {!!columns.filter((props: any) => props?.search).length && (
                            <TableRow>
                                {columns.map((column: any, ci) => (
                                    <TableCell
                                        key={`th-search-cell-${ci}`}
                                        sx={{
                                            top: config?.adjustHeader || 45,
                                            padding: 0,
                                            margin: 0,
                                            fontSize: "14px",
                                            color: "#005075",
                                            lineHeight: "16px",
                                            fontFamily: "Roboto",
                                            fontWeight: 500,
                                            borderTop: 'unset',
                                            textAlign: "left",
                                            'input:focus': {
                                                outline: 'none'
                                            },
                                            'input::placeholder': {
                                                color: '#C1C1C4'
                                            },
                                            backgroundColor: '#F2F5F8',
                                            ".container:after": {
                                                content: "''",
                                                display: "block",
                                                position: "absolute",
                                                borderStyle: "solid",
                                                width: "0",
                                                height: "0",
                                                bottom: "0",
                                                right: "0",
                                                transform: "rotate(45deg)",
                                                borderColor: "transparent transparent transparent #0090D1",
                                                borderWidth: "5px"
                                            }
                                        }}
                                    >
                                        {column?.search &&
                                            column?.search?.type === 'text' ?
                                            (
                                                <CustomTextFilter
                                                    config={config as any}
                                                    column={column}
                                                    submit={({ field, value } : any) => {

                                                        const _page = 1;
                                                        const _pageSize = initialize?.pageSize ?? config?.pagination?.defaultPageSize ?? 10;

                                                        const filteredData: any = vdsTableArgs?.search ? vdsTableArgs.odata.map((item) => {
                                                            let check = false;
                                                            for (let o in item) {
                                                                if (String(item[o]).toLowerCase().includes(vdsTableArgs.search.toLowerCase())) {
                                                                    check = true;
                                                                    break;
                                                                }
                                                            }
                                                            if (check) return item;
                                                            return null;
                                                        }).filter((item) => item) : vdsTableArgs.odata;

                                                        const columnsSearch = {
                                                            ...vdsTableArgs.columnsSearch,
                                                            [field]: value
                                                        };
                                                        const _keys = Object.keys(columnsSearch);
                                                        let _partialData = [...filteredData];

                                                        if (vdsTableArgs?.search !== undefined && vdsTableArgs?.search !== null) {

                                                          _partialData = filteredData.map((item: any) => {
                                                                let check = false;
                                                                for (let o in item) {
                                                                    if (String(item[o]).toLowerCase().includes(vdsTableArgs.search.toLowerCase())) {
                                                                        check = true;
                                                                        break;
                                                                    }
                                                                }
                                                                if (check) return item;
                                                                return null;
                                                          }).filter((item: any) => item);
                                                        }

                                                        _keys.forEach((key) => {
                                                            _partialData = _partialData.filter((el) => String(el[key]).toLowerCase().includes(columnsSearch[key].toLowerCase()));
                                                        });

                                                        if (AsyncDataTypeGuard(data)) {

                                                            const _map = sortingMap?.sortingMap;
                                                            const _sorting = { sort: null, order: null } as any;

                                                            for (let o in _map) {

                                                                if (_map[o]) {
                                                                    _sorting.sort = o;
                                                                    _sorting.order = _map[o];
                                                                    break;
                                                                }
                                                            }

                                                            setVdsTableArgs({
                                                                ...vdsTableArgs,
                                                                loader: true,
                                                            });
                                                            data({
                                                                page: _page,
                                                                pageSize: _pageSize,
                                                                search: vdsTableArgs?.search,
                                                                sorting: _sorting,
                                                                columnsSearch
                                                            })
                                                                .then((result) => {
                                                                    const { data, totalCount } = result;
                                                                    setVdsTableArgs({
                                                                        ...vdsTableArgs,
                                                                        odata: data,
                                                                        data,
                                                                        filteredData: data,
                                                                        loader: false,
                                                                        totalCount,
                                                                        columnsSearch
                                                                    });
                                                                });
                                                        } else {

                                                            setVdsTableArgs({
                                                                ...vdsTableArgs,
                                                                filteredData: _partialData,
                                                                data: _partialData.slice((_page - 1) * _pageSize, ((_page - 1) * _pageSize) + _pageSize),
                                                                totalCount: _partialData.length,
                                                                columnsSearch
                                                            });
                                                            setPage(_page);
                                                        }
                                                    }}
                                                    initialize={initialize?.columnsSearch?.[column?.search?.field]}
                                                />
                                            ) : column?.search?.type === 'select' ?
                                                (
                                                    <CustomSelectFilter
                                                        config={config as any}
                                                        column={column}
                                                        submit={({ field, value }: any) => {

                                                            const _page = 1;
                                                            const _pageSize = initialize?.pageSize ?? config?.pagination?.defaultPageSize ?? 10;

                                                            const filteredData: any = vdsTableArgs?.search ? vdsTableArgs.odata.map((item) => {
                                                                let check = false;
                                                                for (let o in item) {
                                                                    if (String(item[o]).toLowerCase().includes(vdsTableArgs.search.toLowerCase())) {
                                                                        check = true;
                                                                        break;
                                                                    }
                                                                }
                                                                if (check) return item;
                                                                return null;
                                                            }).filter((item) => item) : vdsTableArgs.odata;

                                                            const columnsSearch = {
                                                                ...vdsTableArgs.columnsSearch,
                                                                [field]: value
                                                            };
                                                            const _keys = Object.keys(columnsSearch);
                                                            let _partialData = [...filteredData];

                                                            if (vdsTableArgs?.search !== undefined && vdsTableArgs?.search !== null) {

                                                              _partialData = filteredData.map((item: any) => {
                                                                    let check = false;
                                                                    for (let o in item) {
                                                                        if (String(item[o]).toLowerCase().includes(vdsTableArgs.search.toLowerCase())) {
                                                                            check = true;
                                                                            break;
                                                                        }
                                                                    }
                                                                    if (check) return item;
                                                                    return null;
                                                              }).filter((item: any) => item);
                                                            }

                                                            _keys.forEach((key) => {
                                                                _partialData = _partialData.filter((el) => String(el[key]).toLowerCase().includes(columnsSearch[key].toLowerCase()));
                                                            });

                                                            if (AsyncDataTypeGuard(data)) {

                                                                const _map = sortingMap?.sortingMap;
                                                                const _sorting = { sort: null, order: null } as any;

                                                                for (let o in _map) {

                                                                    if (_map[o]) {
                                                                        _sorting.sort = o;
                                                                        _sorting.order = _map[o];
                                                                        break;
                                                                    }
                                                                }

                                                                setVdsTableArgs({
                                                                    ...vdsTableArgs,
                                                                    loader: true,
                                                                });
                                                                data({
                                                                    page: _page,
                                                                    pageSize: _pageSize,
                                                                    search: vdsTableArgs?.search,
                                                                    sorting: _sorting,
                                                                    columnsSearch
                                                                })
                                                                    .then((result) => {
                                                                        const { data, totalCount } = result;
                                                                        setVdsTableArgs({
                                                                            ...vdsTableArgs,
                                                                            odata: data,
                                                                            data,
                                                                            loader: false,
                                                                            filteredData: data,
                                                                            totalCount,
                                                                            columnsSearch
                                                                        });
                                                                    });
                                                            } else {

                                                                setVdsTableArgs({
                                                                    ...vdsTableArgs,
                                                                    filteredData: _partialData,
                                                                    data: _partialData.slice((_page - 1) * _pageSize, ((_page - 1) * _pageSize) + _pageSize),
                                                                    totalCount: _partialData.length,
                                                                    columnsSearch: {
                                                                        ...vdsTableArgs.columnsSearch,
                                                                        [field]: value
                                                                    }
                                                                });
                                                                setPage(_page);
                                                            }
                                                        }}
                                                        initialize={initialize?.columnsSearch?.[column?.search?.field]}
                                                    />
                                                ) : null
                                        }
                                    </TableCell>
                                ))}
                            </TableRow>
                        )}
                    </TableHead>
                    <TableBody style={{ cursor: 'pointer' }}>
                        {vdsTableArgs?.loader && (
                            <TableRow>
                                <TableCell colSpan={columns.length} sx={{ textAlign: 'center', height: (42 * pageSize) }}>
                                    <CircularProgress />
                                </TableCell>
                            </TableRow>
                        )}
                        {!vdsTableArgs?.loader && !vdsTableArgs.data.length && (
                            <TableRow>
                                <TableCell colSpan={columns.length} sx={{ textAlign: 'center', height: (42 * pageSize) }}>
                                    <div>
                                        {config?.localize?.noData || 'No Data'}
                                    </div>
                                </TableCell>
                            </TableRow>
                        )}
                        {!vdsTableArgs?.loader && !!vdsTableArgs.data.length && vdsTableArgs.data.map((row, ri) => {
                            return (
                                <Row key={`row-${ri}`} row={row} rowindex={ri} />
                            );
                        })}
                    </TableBody>
                </Table>
            </TableContainer>
            <div style={{ display: 'flex', justifyContent: 'end', alignItems: 'center', marginTop: '10px' }}>
                {vdsTableArgs?.loader && config?.pagination?.usePagination && (
                    <>-</>
                )}
                {!vdsTableArgs?.loader && config?.pagination?.usePagination && (
                    <Pagination
                        count={pageSize > 0 ? Math.ceil(totalCount / pageSize) : 0}
                        page={page}
                        shape="rounded"
                        onChange={handlePageChange}
                        sx={{
                            fontSize: '14px',
                            '.MuiPaginationItem-firstLast': {
                                color: '#0090D1'
                            },
                            '.MuiPaginationItem-previousNext': {
                                color: '#0090D1'
                            },
                            '.Mui-selected': {
                                backgroundColor: 'white!important',
                                color: '#0090D1'
                            },
                            'button:hover:not(Mui-selected)': {
                                backgroundColor: '#DEF0F7',
                                color: '#0090D1'
                            }
                        }}
                        showFirstButton
                        showLastButton
                    />
                )}
            </div>

        </div>
    );
};

export const VdsTable = React.forwardRef(VdsTable1) as <R>(
    props: VdsTableProps<R> & {
        ref?: React.ForwardedRef<any>
    }
) => ReturnType<typeof VdsTable1>;
