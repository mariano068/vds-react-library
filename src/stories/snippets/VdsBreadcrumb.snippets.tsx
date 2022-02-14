import { Link, Typography } from '@mui/material'
import * as React from 'react'
import { VdsBreadcrumb } from '../../vds/VdsBreadcrumb/VdsBreadcrumb'
import { convert } from '../utils'


//#region Default example
export const Breadcrumb_Default_Example = () => {

  const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

  return (
    <VdsBreadcrumb>
      <Link onClick={onClickHandler}>Breadcrumb link 1</Link>
      <Link onClick={onClickHandler}>Breadcrumb link 2</Link>
      <Link onClick={onClickHandler}>Breadcrumb link 3</Link>
      <Typography>Text 1</Typography>
    </VdsBreadcrumb>
  )
}
export const breadcrumb_Default_Example_snippet = convert(`
import React from 'react';
import { Breadcrumb } from 'vds-components';

export default () => {

    const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

    return (
      <VdsBreadcrumb>
        <Link onClick={onClickHandler}>Breadcrumb link 1</Link>
        <Link onClick={onClickHandler}>Breadcrumb link 2</Link>
        <Link onClick={onClickHandler}>Breadcrumb link 3</Link>
        <Typography>Text 1</Typography>
      </VdsBreadcrumb>
    );
}
`)
//#endregion
